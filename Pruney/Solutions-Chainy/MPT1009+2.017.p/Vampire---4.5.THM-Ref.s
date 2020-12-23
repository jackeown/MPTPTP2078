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
% DateTime   : Thu Dec  3 13:04:28 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 462 expanded)
%              Number of leaves         :   17 ( 104 expanded)
%              Depth                    :   27
%              Number of atoms          :  244 (1485 expanded)
%              Number of equality atoms :   87 ( 372 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(subsumption_resolution,[],[f204,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f204,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f198,f53])).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

% (2334)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f198,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f176,f180])).

fof(f180,plain,(
    k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f88,f157])).

fof(f157,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f153,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3)) ),
    inference(resolution,[],[f82,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f82,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f72,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f41])).

fof(f41,plain,
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

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f153,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f99,f152])).

fof(f152,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f151,f128])).

fof(f128,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0)) ),
    inference(superposition,[],[f92,f104])).

fof(f104,plain,(
    sK3 = k7_relat_1(sK3,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f102,f82])).

fof(f102,plain,
    ( sK3 = k7_relat_1(sK3,k1_tarski(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f90,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f90,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f73,f49])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f92,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f61,f82])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f151,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k1_tarski(sK0))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f150,f56])).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f150,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f149,f56])).

fof(f149,plain,
    ( k9_relat_1(sK3,k2_tarski(sK0,sK0)) = k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f148,f81])).

fof(f81,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f71,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
     => r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | k9_relat_1(sK3,k2_tarski(X0,sK0)) = k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,sK0))
      | k1_xboole_0 = k1_relat_1(sK3) ) ),
    inference(resolution,[],[f137,f81])).

fof(f137,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_tarski(sK0))
      | ~ r2_hidden(X2,k1_tarski(sK0))
      | k9_relat_1(sK3,k2_tarski(X2,X1)) = k2_tarski(k1_funct_1(sK3,X2),k1_funct_1(sK3,X1))
      | k1_xboole_0 = k1_relat_1(sK3) ) ),
    inference(superposition,[],[f101,f123])).

fof(f123,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f105,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f105,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f103,f82])).

fof(f103,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f90,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ r2_hidden(X1,k1_relat_1(sK3))
      | k9_relat_1(sK3,k2_tarski(X1,X0)) = k2_tarski(k1_funct_1(sK3,X1),k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f100,f82])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ r2_hidden(X1,k1_relat_1(sK3))
      | k9_relat_1(sK3,k2_tarski(X1,X0)) = k2_tarski(k1_funct_1(sK3,X1),k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

fof(f99,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f51,f97])).

fof(f97,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f51,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f82,f57])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f176,plain,(
    ~ r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f99,f171])).

fof(f171,plain,(
    ! [X0] : k2_relat_1(sK3) = k9_relat_1(sK3,X0) ),
    inference(backward_demodulation,[],[f92,f170])).

fof(f170,plain,(
    ! [X0] : sK3 = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f168,f82])).

fof(f168,plain,(
    ! [X0] :
      ( sK3 = k7_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f165,f64])).

fof(f165,plain,(
    ! [X0] : v4_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f158,f54])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v4_relat_1(sK3,X0) ) ),
    inference(backward_demodulation,[],[f86,f157])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | v4_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f82,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:23:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (2332)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.48  % (2332)Refutation not found, incomplete strategy% (2332)------------------------------
% 0.21/0.48  % (2332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2348)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.48  % (2332)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2332)Memory used [KB]: 10746
% 0.21/0.48  % (2332)Time elapsed: 0.052 s
% 0.21/0.48  % (2332)------------------------------
% 0.21/0.48  % (2332)------------------------------
% 0.21/0.48  % (2348)Refutation not found, incomplete strategy% (2348)------------------------------
% 0.21/0.48  % (2348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2348)Memory used [KB]: 6268
% 0.21/0.48  % (2348)Time elapsed: 0.062 s
% 0.21/0.48  % (2348)------------------------------
% 0.21/0.48  % (2348)------------------------------
% 0.21/0.54  % (2330)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (2327)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (2324)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (2326)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (2346)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (2346)Refutation not found, incomplete strategy% (2346)------------------------------
% 0.21/0.56  % (2346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2346)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2346)Memory used [KB]: 10618
% 0.21/0.56  % (2346)Time elapsed: 0.148 s
% 0.21/0.56  % (2346)------------------------------
% 0.21/0.56  % (2346)------------------------------
% 0.21/0.56  % (2333)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (2339)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (2351)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (2323)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.57  % (2323)Refutation not found, incomplete strategy% (2323)------------------------------
% 0.21/0.57  % (2323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (2323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (2323)Memory used [KB]: 1663
% 0.21/0.57  % (2323)Time elapsed: 0.123 s
% 0.21/0.57  % (2323)------------------------------
% 0.21/0.57  % (2323)------------------------------
% 0.21/0.57  % (2331)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (2338)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (2325)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (2338)Refutation not found, incomplete strategy% (2338)------------------------------
% 0.21/0.57  % (2338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (2338)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (2338)Memory used [KB]: 10618
% 0.21/0.57  % (2338)Time elapsed: 0.158 s
% 0.21/0.57  % (2338)------------------------------
% 0.21/0.57  % (2338)------------------------------
% 0.21/0.57  % (2342)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.59/0.57  % (2341)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.59/0.57  % (2347)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.58  % (2350)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.59/0.58  % (2335)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.59/0.58  % (2347)Refutation not found, incomplete strategy% (2347)------------------------------
% 1.59/0.58  % (2347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (2347)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (2347)Memory used [KB]: 6268
% 1.59/0.58  % (2347)Time elapsed: 0.153 s
% 1.59/0.58  % (2347)------------------------------
% 1.59/0.58  % (2347)------------------------------
% 1.59/0.58  % (2340)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.59/0.58  % (2350)Refutation not found, incomplete strategy% (2350)------------------------------
% 1.59/0.58  % (2350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (2350)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (2350)Memory used [KB]: 10746
% 1.59/0.58  % (2350)Time elapsed: 0.157 s
% 1.59/0.58  % (2350)------------------------------
% 1.59/0.58  % (2350)------------------------------
% 1.59/0.58  % (2339)Refutation not found, incomplete strategy% (2339)------------------------------
% 1.59/0.58  % (2339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (2339)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (2339)Memory used [KB]: 1791
% 1.59/0.58  % (2339)Time elapsed: 0.155 s
% 1.59/0.58  % (2339)------------------------------
% 1.59/0.58  % (2339)------------------------------
% 1.59/0.58  % (2329)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.59/0.58  % (2336)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.59/0.58  % (2343)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.59/0.58  % (2349)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.58  % (2336)Refutation not found, incomplete strategy% (2336)------------------------------
% 1.59/0.58  % (2336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (2336)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (2336)Memory used [KB]: 1791
% 1.59/0.58  % (2336)Time elapsed: 0.110 s
% 1.59/0.58  % (2336)------------------------------
% 1.59/0.58  % (2336)------------------------------
% 1.59/0.58  % (2349)Refutation not found, incomplete strategy% (2349)------------------------------
% 1.59/0.58  % (2349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (2349)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (2349)Memory used [KB]: 6268
% 1.59/0.58  % (2349)Time elapsed: 0.165 s
% 1.59/0.58  % (2349)------------------------------
% 1.59/0.58  % (2349)------------------------------
% 1.59/0.58  % (2329)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f205,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(subsumption_resolution,[],[f204,f54])).
% 1.59/0.58  fof(f54,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f2])).
% 1.59/0.58  fof(f2,axiom,(
% 1.59/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.59/0.58  fof(f204,plain,(
% 1.59/0.58    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.59/0.58    inference(forward_demodulation,[],[f198,f53])).
% 1.59/0.58  fof(f53,plain,(
% 1.59/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.59/0.58    inference(cnf_transformation,[],[f13])).
% 1.59/0.58  % (2334)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.59/0.58  fof(f13,axiom,(
% 1.59/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.59/0.58  fof(f198,plain,(
% 1.59/0.58    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.59/0.58    inference(backward_demodulation,[],[f176,f180])).
% 1.59/0.58  fof(f180,plain,(
% 1.59/0.58    k1_xboole_0 = sK3),
% 1.59/0.58    inference(trivial_inequality_removal,[],[f179])).
% 1.59/0.58  fof(f179,plain,(
% 1.59/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3),
% 1.59/0.58    inference(superposition,[],[f88,f157])).
% 1.59/0.58  fof(f157,plain,(
% 1.59/0.58    k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.58    inference(subsumption_resolution,[],[f153,f89])).
% 1.59/0.58  fof(f89,plain,(
% 1.59/0.58    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))) )),
% 1.59/0.58    inference(resolution,[],[f82,f60])).
% 1.59/0.58  fof(f60,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f28])).
% 1.59/0.58  fof(f28,plain,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f10])).
% 1.59/0.58  fof(f10,axiom,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.59/0.58  fof(f82,plain,(
% 1.59/0.58    v1_relat_1(sK3)),
% 1.59/0.58    inference(resolution,[],[f72,f49])).
% 1.59/0.58  fof(f49,plain,(
% 1.59/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f42,plain,(
% 1.59/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f41])).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.59/0.58    inference(flattening,[],[f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.59/0.58    inference(ennf_transformation,[],[f22])).
% 1.59/0.58  fof(f22,plain,(
% 1.59/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.59/0.58    inference(pure_predicate_removal,[],[f20])).
% 1.59/0.58  fof(f20,negated_conjecture,(
% 1.59/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.59/0.58    inference(negated_conjecture,[],[f19])).
% 1.59/0.58  fof(f19,conjecture,(
% 1.59/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.59/0.58  fof(f72,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f34])).
% 1.59/0.58  fof(f34,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.58    inference(ennf_transformation,[],[f16])).
% 1.59/0.58  fof(f16,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.59/0.58  fof(f153,plain,(
% 1.59/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.58    inference(superposition,[],[f99,f152])).
% 1.59/0.58  fof(f152,plain,(
% 1.59/0.58    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.58    inference(forward_demodulation,[],[f151,f128])).
% 1.59/0.58  fof(f128,plain,(
% 1.59/0.58    k2_relat_1(sK3) = k9_relat_1(sK3,k1_tarski(sK0))),
% 1.59/0.58    inference(superposition,[],[f92,f104])).
% 1.59/0.58  fof(f104,plain,(
% 1.59/0.58    sK3 = k7_relat_1(sK3,k1_tarski(sK0))),
% 1.59/0.58    inference(subsumption_resolution,[],[f102,f82])).
% 1.59/0.58  fof(f102,plain,(
% 1.59/0.58    sK3 = k7_relat_1(sK3,k1_tarski(sK0)) | ~v1_relat_1(sK3)),
% 1.59/0.58    inference(resolution,[],[f90,f64])).
% 1.59/0.58  fof(f64,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f32])).
% 1.59/0.58  fof(f32,plain,(
% 1.59/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(flattening,[],[f31])).
% 1.59/0.58  fof(f31,plain,(
% 1.59/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f12])).
% 1.59/0.58  fof(f12,axiom,(
% 1.59/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.59/0.58  fof(f90,plain,(
% 1.59/0.58    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.59/0.58    inference(resolution,[],[f73,f49])).
% 1.59/0.58  fof(f73,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f35])).
% 1.59/0.58  fof(f35,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.58    inference(ennf_transformation,[],[f23])).
% 1.59/0.58  fof(f23,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.59/0.58    inference(pure_predicate_removal,[],[f17])).
% 1.59/0.58  fof(f17,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.59/0.58  fof(f92,plain,(
% 1.59/0.58    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) )),
% 1.59/0.58    inference(resolution,[],[f61,f82])).
% 1.59/0.58  fof(f61,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.59/0.58    inference(cnf_transformation,[],[f29])).
% 1.59/0.58  fof(f29,plain,(
% 1.59/0.58    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f11])).
% 1.59/0.58  fof(f11,axiom,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.59/0.58  fof(f151,plain,(
% 1.59/0.58    k1_tarski(k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k1_tarski(sK0)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.58    inference(forward_demodulation,[],[f150,f56])).
% 1.59/0.58  fof(f56,plain,(
% 1.59/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f3])).
% 1.59/0.58  fof(f3,axiom,(
% 1.59/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.58  fof(f150,plain,(
% 1.59/0.58    k1_tarski(k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_tarski(sK0,sK0)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.58    inference(forward_demodulation,[],[f149,f56])).
% 1.59/0.58  fof(f149,plain,(
% 1.59/0.58    k9_relat_1(sK3,k2_tarski(sK0,sK0)) = k2_tarski(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.58    inference(resolution,[],[f148,f81])).
% 1.59/0.58  fof(f81,plain,(
% 1.59/0.58    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.59/0.58    inference(resolution,[],[f71,f77])).
% 1.59/0.58  fof(f77,plain,(
% 1.59/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.59/0.58    inference(equality_resolution,[],[f66])).
% 1.59/0.58  fof(f66,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.59/0.58    inference(cnf_transformation,[],[f45])).
% 1.59/0.58  fof(f45,plain,(
% 1.59/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.58    inference(flattening,[],[f44])).
% 1.59/0.58  fof(f44,plain,(
% 1.59/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.58    inference(nnf_transformation,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.58  fof(f71,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f33])).
% 1.59/0.58  fof(f33,plain,(
% 1.59/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f21])).
% 1.59/0.58  fof(f21,plain,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) => r2_hidden(X0,X1))),
% 1.59/0.58    inference(unused_predicate_definition_removal,[],[f5])).
% 1.59/0.58  fof(f5,axiom,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.59/0.58  fof(f148,plain,(
% 1.59/0.58    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | k9_relat_1(sK3,k2_tarski(X0,sK0)) = k2_tarski(k1_funct_1(sK3,X0),k1_funct_1(sK3,sK0)) | k1_xboole_0 = k1_relat_1(sK3)) )),
% 1.59/0.58    inference(resolution,[],[f137,f81])).
% 1.59/0.58  fof(f137,plain,(
% 1.59/0.58    ( ! [X2,X1] : (~r2_hidden(X1,k1_tarski(sK0)) | ~r2_hidden(X2,k1_tarski(sK0)) | k9_relat_1(sK3,k2_tarski(X2,X1)) = k2_tarski(k1_funct_1(sK3,X2),k1_funct_1(sK3,X1)) | k1_xboole_0 = k1_relat_1(sK3)) )),
% 1.59/0.58    inference(superposition,[],[f101,f123])).
% 1.59/0.58  fof(f123,plain,(
% 1.59/0.58    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.58    inference(resolution,[],[f105,f68])).
% 1.59/0.58  fof(f68,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.59/0.58    inference(cnf_transformation,[],[f47])).
% 1.59/0.58  fof(f47,plain,(
% 1.59/0.58    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.59/0.58    inference(flattening,[],[f46])).
% 1.59/0.58  fof(f46,plain,(
% 1.59/0.58    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.59/0.58    inference(nnf_transformation,[],[f6])).
% 1.59/0.58  fof(f6,axiom,(
% 1.59/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.59/0.58  fof(f105,plain,(
% 1.59/0.58    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 1.59/0.58    inference(subsumption_resolution,[],[f103,f82])).
% 1.59/0.58  fof(f103,plain,(
% 1.59/0.58    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3)),
% 1.59/0.58    inference(resolution,[],[f90,f62])).
% 1.59/0.58  fof(f62,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f43])).
% 1.59/0.58  fof(f43,plain,(
% 1.59/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(nnf_transformation,[],[f30])).
% 1.59/0.58  fof(f30,plain,(
% 1.59/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.59/0.58  fof(f101,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(X1,k1_relat_1(sK3)) | k9_relat_1(sK3,k2_tarski(X1,X0)) = k2_tarski(k1_funct_1(sK3,X1),k1_funct_1(sK3,X0))) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f100,f82])).
% 1.59/0.58  fof(f100,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(X1,k1_relat_1(sK3)) | k9_relat_1(sK3,k2_tarski(X1,X0)) = k2_tarski(k1_funct_1(sK3,X1),k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 1.59/0.58    inference(resolution,[],[f74,f48])).
% 1.59/0.58  fof(f48,plain,(
% 1.59/0.58    v1_funct_1(sK3)),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f74,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f37])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.59/0.58    inference(flattening,[],[f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.59/0.58    inference(ennf_transformation,[],[f15])).
% 1.59/0.58  fof(f15,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).
% 1.59/0.58  fof(f99,plain,(
% 1.59/0.58    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.59/0.58    inference(backward_demodulation,[],[f51,f97])).
% 1.59/0.58  fof(f97,plain,(
% 1.59/0.58    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),sK1,sK3,X0)) )),
% 1.59/0.58    inference(resolution,[],[f76,f49])).
% 1.59/0.58  fof(f76,plain,(
% 1.59/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f40,plain,(
% 1.59/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.58    inference(ennf_transformation,[],[f18])).
% 1.59/0.58  fof(f18,axiom,(
% 1.59/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.59/0.58  fof(f51,plain,(
% 1.59/0.58    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f88,plain,(
% 1.59/0.58    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = sK3),
% 1.59/0.58    inference(resolution,[],[f82,f57])).
% 1.59/0.58  fof(f57,plain,(
% 1.59/0.58    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f27,plain,(
% 1.59/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.59/0.58    inference(flattening,[],[f26])).
% 1.59/0.58  fof(f26,plain,(
% 1.59/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f14])).
% 1.59/0.58  fof(f14,axiom,(
% 1.59/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.59/0.58  fof(f176,plain,(
% 1.59/0.58    ~r1_tarski(k2_relat_1(sK3),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.59/0.58    inference(backward_demodulation,[],[f99,f171])).
% 1.59/0.58  fof(f171,plain,(
% 1.59/0.58    ( ! [X0] : (k2_relat_1(sK3) = k9_relat_1(sK3,X0)) )),
% 1.59/0.58    inference(backward_demodulation,[],[f92,f170])).
% 1.59/0.58  fof(f170,plain,(
% 1.59/0.58    ( ! [X0] : (sK3 = k7_relat_1(sK3,X0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f168,f82])).
% 1.59/0.58  fof(f168,plain,(
% 1.59/0.58    ( ! [X0] : (sK3 = k7_relat_1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 1.59/0.58    inference(resolution,[],[f165,f64])).
% 1.59/0.58  fof(f165,plain,(
% 1.59/0.58    ( ! [X0] : (v4_relat_1(sK3,X0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f158,f54])).
% 1.59/0.58  fof(f158,plain,(
% 1.59/0.58    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v4_relat_1(sK3,X0)) )),
% 1.59/0.58    inference(backward_demodulation,[],[f86,f157])).
% 1.59/0.58  fof(f86,plain,(
% 1.59/0.58    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | v4_relat_1(sK3,X0)) )),
% 1.59/0.58    inference(resolution,[],[f82,f63])).
% 1.59/0.58  fof(f63,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f43])).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (2329)------------------------------
% 1.59/0.58  % (2329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (2329)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (2329)Memory used [KB]: 1791
% 1.59/0.58  % (2329)Time elapsed: 0.165 s
% 1.59/0.58  % (2329)------------------------------
% 1.59/0.58  % (2329)------------------------------
% 1.59/0.59  % (2322)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.59/0.59  % (2321)Success in time 0.218 s
%------------------------------------------------------------------------------

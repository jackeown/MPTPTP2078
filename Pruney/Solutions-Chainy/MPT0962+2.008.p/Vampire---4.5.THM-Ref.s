%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:22 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 436 expanded)
%              Number of leaves         :   18 ( 108 expanded)
%              Depth                    :   25
%              Number of atoms          :  292 (1691 expanded)
%              Number of equality atoms :   78 ( 344 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1422,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1421,f84])).

fof(f84,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1421,plain,(
    sP0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f1420,f274])).

fof(f274,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f263,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f263,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f251,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f251,plain,(
    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f244,f178])).

fof(f178,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f160,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f160,plain,(
    ! [X4] : v1_relat_1(k2_zfmisc_1(k2_relat_1(sK4),X4)) ),
    inference(resolution,[],[f114,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,(
    ! [X4] : m1_subset_1(k2_zfmisc_1(k2_relat_1(sK4),X4),k1_zfmisc_1(k2_zfmisc_1(sK3,X4))) ),
    inference(resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f88,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k2_relat_1(sK4),X0),k2_zfmisc_1(sK3,X0)) ),
    inference(resolution,[],[f48,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f48,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
      | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
      | ~ v1_funct_1(sK4) )
    & r1_tarski(k2_relat_1(sK4),sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
        | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
        | ~ v1_funct_1(sK4) )
      & r1_tarski(k2_relat_1(sK4),sK3)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f244,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f242,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f242,plain,(
    v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f190,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f190,plain,(
    ! [X2] : v4_relat_1(k2_zfmisc_1(X2,k2_relat_1(sK4)),X2) ),
    inference(resolution,[],[f126,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f126,plain,(
    ! [X4] : m1_subset_1(k2_zfmisc_1(X4,k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X4,sK3))) ),
    inference(resolution,[],[f89,f59])).

fof(f89,plain,(
    ! [X1] : r1_tarski(k2_zfmisc_1(X1,k2_relat_1(sK4)),k2_zfmisc_1(X1,sK3)) ),
    inference(resolution,[],[f48,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1420,plain,(
    sP0(k1_relat_1(k1_xboole_0),sK3) ),
    inference(forward_demodulation,[],[f1419,f1260])).

fof(f1260,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f1256,f89])).

fof(f1256,plain,
    ( k1_xboole_0 = sK4
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),k2_zfmisc_1(k1_relat_1(sK4),sK3)) ),
    inference(resolution,[],[f1191,f632])).

fof(f632,plain,(
    ! [X0] :
      ( r1_tarski(sK4,X0)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),X0) ) ),
    inference(superposition,[],[f65,f106])).

fof(f106,plain,(
    k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)) = k2_xboole_0(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f87,plain,(
    r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f46,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1191,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK3))
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f793,f59])).

fof(f793,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f782,f50])).

fof(f782,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | k1_xboole_0 = sK4
    | ~ r1_tarski(k1_xboole_0,sK4) ),
    inference(resolution,[],[f357,f57])).

fof(f357,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(forward_demodulation,[],[f356,f79])).

fof(f356,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(subsumption_resolution,[],[f342,f50])).

fof(f342,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK4))
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(superposition,[],[f134,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(resolution,[],[f123,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f123,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(subsumption_resolution,[],[f122,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f122,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | k1_relat_1(sK4) != k1_relset_1(k1_relat_1(sK4),sK3,sK4)
    | sP0(k1_relat_1(sK4),sK3) ),
    inference(subsumption_resolution,[],[f121,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f28,f31,f30,f29])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f121,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | k1_relat_1(sK4) != k1_relset_1(k1_relat_1(sK4),sK3,sK4)
    | sP0(k1_relat_1(sK4),sK3)
    | ~ sP1(k1_relat_1(sK4),sK4,sK3) ),
    inference(resolution,[],[f98,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f98,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(subsumption_resolution,[],[f49,f47])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f134,plain,
    ( ~ r1_tarski(sK3,k2_relat_1(sK4))
    | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK3)) ),
    inference(superposition,[],[f87,f91])).

fof(f91,plain,
    ( sK3 = k2_relat_1(sK4)
    | ~ r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(resolution,[],[f48,f57])).

fof(f1419,plain,(
    sP0(k1_relat_1(sK4),sK3) ),
    inference(subsumption_resolution,[],[f1418,f165])).

fof(f165,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f163,f79])).

fof(f163,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) ),
    inference(superposition,[],[f114,f79])).

fof(f1418,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | sP0(k1_relat_1(sK4),sK3) ),
    inference(forward_demodulation,[],[f1417,f80])).

fof(f1417,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | sP0(k1_relat_1(sK4),sK3) ),
    inference(forward_demodulation,[],[f1295,f274])).

fof(f1295,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK3)))
    | sP0(k1_relat_1(sK4),sK3) ),
    inference(backward_demodulation,[],[f123,f1260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:36:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (5571)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (5576)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (5581)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (5576)Refutation not found, incomplete strategy% (5576)------------------------------
% 0.21/0.51  % (5576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5576)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5576)Memory used [KB]: 10618
% 0.21/0.51  % (5576)Time elapsed: 0.080 s
% 0.21/0.51  % (5576)------------------------------
% 0.21/0.51  % (5576)------------------------------
% 0.21/0.51  % (5592)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (5594)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (5575)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (5573)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (5570)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (5584)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.22/0.52  % (5571)Refutation not found, incomplete strategy% (5571)------------------------------
% 1.22/0.52  % (5571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (5571)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (5571)Memory used [KB]: 10618
% 1.22/0.52  % (5571)Time elapsed: 0.112 s
% 1.22/0.52  % (5571)------------------------------
% 1.22/0.52  % (5571)------------------------------
% 1.22/0.52  % (5593)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.22/0.52  % (5586)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.22/0.52  % (5577)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.22/0.52  % (5585)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.22/0.53  % (5579)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.22/0.53  % (5583)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.22/0.53  % (5588)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.22/0.53  % (5589)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.22/0.53  % (5572)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.22/0.53  % (5578)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.22/0.53  % (5587)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.22/0.53  % (5574)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.37/0.54  % (5595)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.37/0.54  % (5591)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.37/0.54  % (5590)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.37/0.54  % (5580)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.37/0.54  % (5582)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.37/0.60  % (5578)Refutation found. Thanks to Tanya!
% 1.37/0.60  % SZS status Theorem for theBenchmark
% 1.37/0.60  % SZS output start Proof for theBenchmark
% 1.37/0.60  fof(f1422,plain,(
% 1.37/0.60    $false),
% 1.37/0.60    inference(subsumption_resolution,[],[f1421,f84])).
% 1.37/0.60  fof(f84,plain,(
% 1.37/0.60    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 1.37/0.60    inference(equality_resolution,[],[f74])).
% 1.37/0.60  fof(f74,plain,(
% 1.37/0.60    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f45])).
% 1.37/0.60  fof(f45,plain,(
% 1.37/0.60    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.37/0.60    inference(nnf_transformation,[],[f29])).
% 1.37/0.60  fof(f29,plain,(
% 1.37/0.60    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.37/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.37/0.60  fof(f1421,plain,(
% 1.37/0.60    sP0(k1_xboole_0,sK3)),
% 1.37/0.60    inference(forward_demodulation,[],[f1420,f274])).
% 1.37/0.60  fof(f274,plain,(
% 1.37/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.37/0.60    inference(subsumption_resolution,[],[f263,f50])).
% 1.37/0.60  fof(f50,plain,(
% 1.37/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f4])).
% 1.37/0.60  fof(f4,axiom,(
% 1.37/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.37/0.60  fof(f263,plain,(
% 1.37/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 1.37/0.60    inference(resolution,[],[f251,f57])).
% 1.37/0.60  fof(f57,plain,(
% 1.37/0.60    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f37])).
% 1.37/0.60  fof(f37,plain,(
% 1.37/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.60    inference(flattening,[],[f36])).
% 1.37/0.60  fof(f36,plain,(
% 1.37/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.37/0.60    inference(nnf_transformation,[],[f1])).
% 1.37/0.60  fof(f1,axiom,(
% 1.37/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.60  fof(f251,plain,(
% 1.37/0.60    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.37/0.60    inference(subsumption_resolution,[],[f244,f178])).
% 1.37/0.60  fof(f178,plain,(
% 1.37/0.60    v1_relat_1(k1_xboole_0)),
% 1.37/0.60    inference(superposition,[],[f160,f79])).
% 1.37/0.60  fof(f79,plain,(
% 1.37/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.37/0.60    inference(equality_resolution,[],[f62])).
% 1.37/0.60  fof(f62,plain,(
% 1.37/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.37/0.60    inference(cnf_transformation,[],[f40])).
% 1.37/0.60  fof(f40,plain,(
% 1.37/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.37/0.60    inference(flattening,[],[f39])).
% 1.37/0.60  fof(f39,plain,(
% 1.37/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.37/0.60    inference(nnf_transformation,[],[f5])).
% 1.37/0.60  fof(f5,axiom,(
% 1.37/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.37/0.60  fof(f160,plain,(
% 1.37/0.60    ( ! [X4] : (v1_relat_1(k2_zfmisc_1(k2_relat_1(sK4),X4))) )),
% 1.37/0.60    inference(resolution,[],[f114,f66])).
% 1.37/0.60  fof(f66,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.60    inference(cnf_transformation,[],[f24])).
% 1.37/0.60  fof(f24,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.60    inference(ennf_transformation,[],[f10])).
% 1.37/0.60  fof(f10,axiom,(
% 1.37/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.37/0.60  fof(f114,plain,(
% 1.37/0.60    ( ! [X4] : (m1_subset_1(k2_zfmisc_1(k2_relat_1(sK4),X4),k1_zfmisc_1(k2_zfmisc_1(sK3,X4)))) )),
% 1.37/0.60    inference(resolution,[],[f88,f59])).
% 1.37/0.60  fof(f59,plain,(
% 1.37/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f38])).
% 1.37/0.60  fof(f38,plain,(
% 1.37/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.37/0.60    inference(nnf_transformation,[],[f7])).
% 1.37/0.60  fof(f7,axiom,(
% 1.37/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.37/0.60  fof(f88,plain,(
% 1.37/0.60    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k2_relat_1(sK4),X0),k2_zfmisc_1(sK3,X0))) )),
% 1.37/0.60    inference(resolution,[],[f48,f63])).
% 1.37/0.60  fof(f63,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f22])).
% 1.37/0.60  fof(f22,plain,(
% 1.37/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.37/0.60    inference(ennf_transformation,[],[f6])).
% 1.37/0.60  fof(f6,axiom,(
% 1.37/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.37/0.60  fof(f48,plain,(
% 1.37/0.60    r1_tarski(k2_relat_1(sK4),sK3)),
% 1.37/0.60    inference(cnf_transformation,[],[f34])).
% 1.37/0.60  fof(f34,plain,(
% 1.37/0.60    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)) & r1_tarski(k2_relat_1(sK4),sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 1.37/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f33])).
% 1.37/0.60  fof(f33,plain,(
% 1.37/0.60    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)) & r1_tarski(k2_relat_1(sK4),sK3) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 1.37/0.60    introduced(choice_axiom,[])).
% 1.37/0.60  fof(f18,plain,(
% 1.37/0.60    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.37/0.60    inference(flattening,[],[f17])).
% 1.37/0.60  fof(f17,plain,(
% 1.37/0.60    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.37/0.60    inference(ennf_transformation,[],[f15])).
% 1.37/0.60  fof(f15,negated_conjecture,(
% 1.37/0.60    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.37/0.60    inference(negated_conjecture,[],[f14])).
% 1.37/0.60  fof(f14,conjecture,(
% 1.37/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.37/0.60  fof(f244,plain,(
% 1.37/0.60    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.37/0.60    inference(resolution,[],[f242,f52])).
% 1.37/0.60  fof(f52,plain,(
% 1.37/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f35])).
% 1.37/0.60  fof(f35,plain,(
% 1.37/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.37/0.60    inference(nnf_transformation,[],[f20])).
% 1.37/0.60  fof(f20,plain,(
% 1.37/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.37/0.60    inference(ennf_transformation,[],[f8])).
% 1.37/0.60  fof(f8,axiom,(
% 1.37/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.37/0.60  fof(f242,plain,(
% 1.37/0.60    v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.37/0.60    inference(superposition,[],[f190,f80])).
% 1.37/0.60  fof(f80,plain,(
% 1.37/0.60    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.37/0.60    inference(equality_resolution,[],[f61])).
% 1.37/0.60  fof(f61,plain,(
% 1.37/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.37/0.60    inference(cnf_transformation,[],[f40])).
% 1.37/0.60  fof(f190,plain,(
% 1.37/0.60    ( ! [X2] : (v4_relat_1(k2_zfmisc_1(X2,k2_relat_1(sK4)),X2)) )),
% 1.37/0.60    inference(resolution,[],[f126,f68])).
% 1.37/0.60  fof(f68,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.60    inference(cnf_transformation,[],[f26])).
% 1.37/0.60  fof(f26,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.60    inference(ennf_transformation,[],[f16])).
% 1.37/0.60  fof(f16,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.37/0.60    inference(pure_predicate_removal,[],[f11])).
% 1.37/0.60  fof(f11,axiom,(
% 1.37/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.37/0.60  fof(f126,plain,(
% 1.37/0.60    ( ! [X4] : (m1_subset_1(k2_zfmisc_1(X4,k2_relat_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(X4,sK3)))) )),
% 1.37/0.60    inference(resolution,[],[f89,f59])).
% 1.37/0.60  fof(f89,plain,(
% 1.37/0.60    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(sK4)),k2_zfmisc_1(X1,sK3))) )),
% 1.37/0.60    inference(resolution,[],[f48,f64])).
% 1.37/0.60  fof(f64,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f22])).
% 1.37/0.60  fof(f1420,plain,(
% 1.37/0.60    sP0(k1_relat_1(k1_xboole_0),sK3)),
% 1.37/0.60    inference(forward_demodulation,[],[f1419,f1260])).
% 1.37/0.60  fof(f1260,plain,(
% 1.37/0.60    k1_xboole_0 = sK4),
% 1.37/0.60    inference(subsumption_resolution,[],[f1256,f89])).
% 1.37/0.60  fof(f1256,plain,(
% 1.37/0.60    k1_xboole_0 = sK4 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),k2_zfmisc_1(k1_relat_1(sK4),sK3))),
% 1.37/0.60    inference(resolution,[],[f1191,f632])).
% 1.37/0.60  fof(f632,plain,(
% 1.37/0.60    ( ! [X0] : (r1_tarski(sK4,X0) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)),X0)) )),
% 1.37/0.60    inference(superposition,[],[f65,f106])).
% 1.37/0.60  fof(f106,plain,(
% 1.37/0.60    k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)) = k2_xboole_0(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))),
% 1.37/0.60    inference(resolution,[],[f87,f54])).
% 1.37/0.60  fof(f54,plain,(
% 1.37/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f21])).
% 1.37/0.60  fof(f21,plain,(
% 1.37/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.37/0.60    inference(ennf_transformation,[],[f3])).
% 1.37/0.60  fof(f3,axiom,(
% 1.37/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.37/0.60  fof(f87,plain,(
% 1.37/0.60    r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))),
% 1.37/0.60    inference(resolution,[],[f46,f51])).
% 1.37/0.60  fof(f51,plain,(
% 1.37/0.60    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f19])).
% 1.37/0.60  fof(f19,plain,(
% 1.37/0.60    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.37/0.60    inference(ennf_transformation,[],[f9])).
% 1.37/0.60  fof(f9,axiom,(
% 1.37/0.60    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.37/0.60  fof(f46,plain,(
% 1.37/0.60    v1_relat_1(sK4)),
% 1.37/0.60    inference(cnf_transformation,[],[f34])).
% 1.37/0.60  fof(f65,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f23])).
% 1.37/0.60  fof(f23,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.37/0.60    inference(ennf_transformation,[],[f2])).
% 1.37/0.60  fof(f2,axiom,(
% 1.37/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.37/0.60  fof(f1191,plain,(
% 1.37/0.60    ~r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK3)) | k1_xboole_0 = sK4),
% 1.37/0.60    inference(resolution,[],[f793,f59])).
% 1.37/0.60  fof(f793,plain,(
% 1.37/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | k1_xboole_0 = sK4),
% 1.37/0.60    inference(subsumption_resolution,[],[f782,f50])).
% 1.37/0.60  fof(f782,plain,(
% 1.37/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | k1_xboole_0 = sK4 | ~r1_tarski(k1_xboole_0,sK4)),
% 1.37/0.60    inference(resolution,[],[f357,f57])).
% 1.37/0.60  fof(f357,plain,(
% 1.37/0.60    r1_tarski(sK4,k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 1.37/0.60    inference(forward_demodulation,[],[f356,f79])).
% 1.37/0.60  fof(f356,plain,(
% 1.37/0.60    r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 1.37/0.60    inference(subsumption_resolution,[],[f342,f50])).
% 1.37/0.60  fof(f342,plain,(
% 1.37/0.60    ~r1_tarski(k1_xboole_0,k2_relat_1(sK4)) | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 1.37/0.60    inference(superposition,[],[f134,f148])).
% 1.37/0.60  fof(f148,plain,(
% 1.37/0.60    k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 1.37/0.60    inference(resolution,[],[f123,f73])).
% 1.37/0.60  fof(f73,plain,(
% 1.37/0.60    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP0(X0,X1)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f45])).
% 1.37/0.60  fof(f123,plain,(
% 1.37/0.60    sP0(k1_relat_1(sK4),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 1.37/0.60    inference(subsumption_resolution,[],[f122,f67])).
% 1.37/0.60  fof(f67,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.60    inference(cnf_transformation,[],[f25])).
% 1.37/0.60  fof(f25,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.60    inference(ennf_transformation,[],[f12])).
% 1.37/0.60  fof(f12,axiom,(
% 1.37/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.37/0.60  fof(f122,plain,(
% 1.37/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | k1_relat_1(sK4) != k1_relset_1(k1_relat_1(sK4),sK3,sK4) | sP0(k1_relat_1(sK4),sK3)),
% 1.37/0.60    inference(subsumption_resolution,[],[f121,f75])).
% 1.37/0.60  fof(f75,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.37/0.60    inference(cnf_transformation,[],[f32])).
% 1.37/0.60  fof(f32,plain,(
% 1.37/0.60    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.60    inference(definition_folding,[],[f28,f31,f30,f29])).
% 1.37/0.60  fof(f30,plain,(
% 1.37/0.60    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.37/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.37/0.60  fof(f31,plain,(
% 1.37/0.60    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.37/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.37/0.60  fof(f28,plain,(
% 1.37/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.60    inference(flattening,[],[f27])).
% 1.37/0.60  fof(f27,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.60    inference(ennf_transformation,[],[f13])).
% 1.37/0.60  fof(f13,axiom,(
% 1.37/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.37/0.60  fof(f121,plain,(
% 1.37/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | k1_relat_1(sK4) != k1_relset_1(k1_relat_1(sK4),sK3,sK4) | sP0(k1_relat_1(sK4),sK3) | ~sP1(k1_relat_1(sK4),sK4,sK3)),
% 1.37/0.60    inference(resolution,[],[f98,f72])).
% 1.37/0.60  fof(f72,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f44])).
% 1.37/0.60  fof(f44,plain,(
% 1.37/0.60    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.37/0.60    inference(rectify,[],[f43])).
% 1.37/0.60  fof(f43,plain,(
% 1.37/0.60    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.37/0.60    inference(nnf_transformation,[],[f30])).
% 1.37/0.60  fof(f98,plain,(
% 1.37/0.60    ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 1.37/0.60    inference(subsumption_resolution,[],[f49,f47])).
% 1.37/0.60  fof(f47,plain,(
% 1.37/0.60    v1_funct_1(sK4)),
% 1.37/0.60    inference(cnf_transformation,[],[f34])).
% 1.37/0.60  fof(f49,plain,(
% 1.37/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)),
% 1.37/0.60    inference(cnf_transformation,[],[f34])).
% 1.37/0.60  fof(f134,plain,(
% 1.37/0.60    ~r1_tarski(sK3,k2_relat_1(sK4)) | r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),sK3))),
% 1.37/0.60    inference(superposition,[],[f87,f91])).
% 1.37/0.60  fof(f91,plain,(
% 1.37/0.60    sK3 = k2_relat_1(sK4) | ~r1_tarski(sK3,k2_relat_1(sK4))),
% 1.37/0.60    inference(resolution,[],[f48,f57])).
% 1.37/0.60  fof(f1419,plain,(
% 1.37/0.60    sP0(k1_relat_1(sK4),sK3)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1418,f165])).
% 1.37/0.60  fof(f165,plain,(
% 1.37/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.37/0.60    inference(forward_demodulation,[],[f163,f79])).
% 1.37/0.60  fof(f163,plain,(
% 1.37/0.60    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))),
% 1.37/0.60    inference(superposition,[],[f114,f79])).
% 1.37/0.60  fof(f1418,plain,(
% 1.37/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | sP0(k1_relat_1(sK4),sK3)),
% 1.37/0.60    inference(forward_demodulation,[],[f1417,f80])).
% 1.37/0.60  fof(f1417,plain,(
% 1.37/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) | sP0(k1_relat_1(sK4),sK3)),
% 1.37/0.60    inference(forward_demodulation,[],[f1295,f274])).
% 1.37/0.60  fof(f1295,plain,(
% 1.37/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),sK3))) | sP0(k1_relat_1(sK4),sK3)),
% 1.37/0.60    inference(backward_demodulation,[],[f123,f1260])).
% 1.37/0.60  % SZS output end Proof for theBenchmark
% 1.37/0.60  % (5578)------------------------------
% 1.37/0.60  % (5578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.60  % (5578)Termination reason: Refutation
% 1.37/0.60  
% 1.37/0.60  % (5578)Memory used [KB]: 2174
% 1.37/0.60  % (5578)Time elapsed: 0.179 s
% 1.37/0.60  % (5578)------------------------------
% 1.37/0.60  % (5578)------------------------------
% 1.37/0.60  % (5569)Success in time 0.237 s
%------------------------------------------------------------------------------

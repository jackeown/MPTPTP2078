%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:27 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 322 expanded)
%              Number of leaves         :   17 (  72 expanded)
%              Depth                    :   22
%              Number of atoms          :  269 (1112 expanded)
%              Number of equality atoms :  102 ( 334 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14863)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f556,plain,(
    $false ),
    inference(subsumption_resolution,[],[f555,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f555,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f527,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f527,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f114,f517])).

fof(f517,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f516,f49])).

fof(f516,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f515,f81])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f515,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f514,f488])).

fof(f488,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f475,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3)) ),
    inference(resolution,[],[f93,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f93,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f34])).

fof(f34,plain,
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

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f475,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f114,f312])).

fof(f312,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(equality_resolution,[],[f216])).

fof(f216,plain,(
    ! [X1] :
      ( k1_tarski(X1) != k1_tarski(sK0)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X1))
      | k1_xboole_0 = k1_relat_1(sK3) ) ),
    inference(superposition,[],[f118,f159])).

fof(f159,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f125,f127])).

fof(f127,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f126,f93])).

fof(f126,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f103,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f103,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f70,f46])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tarski(X0))
      | k1_tarski(X0) = X1
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tarski(X0))
      | k1_tarski(X0) = X1
      | k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1 ) ),
    inference(superposition,[],[f72,f51])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f118,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f117,f93])).

fof(f117,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f514,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) ),
    inference(forward_demodulation,[],[f505,f81])).

fof(f505,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) ),
    inference(backward_demodulation,[],[f306,f488])).

fof(f306,plain,
    ( sK3 = k2_zfmisc_1(k1_relat_1(sK3),sK1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) ),
    inference(resolution,[],[f267,f61])).

fof(f61,plain,(
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

fof(f267,plain,(
    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1)) ),
    inference(resolution,[],[f219,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f219,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    inference(resolution,[],[f180,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f180,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) ) ),
    inference(resolution,[],[f119,f116])).

fof(f116,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f115,f93])).

fof(f115,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f106,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f106,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f71,f46])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X0)
      | ~ r1_tarski(k1_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f68,f93])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f114,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f48,f111])).

fof(f111,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) ),
    inference(resolution,[],[f77,f46])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (14854)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (14852)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (14878)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (14859)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (14851)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.56  % (14852)Refutation not found, incomplete strategy% (14852)------------------------------
% 0.21/0.56  % (14852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14878)Refutation not found, incomplete strategy% (14878)------------------------------
% 0.21/0.57  % (14878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14878)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14878)Memory used [KB]: 6268
% 0.21/0.57  % (14878)Time elapsed: 0.156 s
% 0.21/0.57  % (14878)------------------------------
% 0.21/0.57  % (14878)------------------------------
% 0.21/0.57  % (14852)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14852)Memory used [KB]: 1791
% 0.21/0.57  % (14852)Time elapsed: 0.125 s
% 0.21/0.57  % (14852)------------------------------
% 0.21/0.57  % (14852)------------------------------
% 0.21/0.57  % (14870)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.58  % (14867)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.59  % (14858)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.59  % (14855)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.59  % (14868)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.60  % (14867)Refutation not found, incomplete strategy% (14867)------------------------------
% 0.21/0.60  % (14867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (14867)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (14867)Memory used [KB]: 10618
% 0.21/0.60  % (14867)Time elapsed: 0.163 s
% 0.21/0.60  % (14867)------------------------------
% 0.21/0.60  % (14867)------------------------------
% 0.21/0.60  % (14857)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.60  % (14853)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.60  % (14860)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.60  % (14861)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.61  % (14874)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.61  % (14868)Refutation not found, incomplete strategy% (14868)------------------------------
% 0.21/0.61  % (14868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (14868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (14868)Memory used [KB]: 1791
% 0.21/0.61  % (14868)Time elapsed: 0.163 s
% 0.21/0.61  % (14868)------------------------------
% 0.21/0.61  % (14868)------------------------------
% 1.82/0.62  % (14856)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.82/0.62  % (14877)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.82/0.62  % (14866)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.82/0.62  % (14880)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.82/0.63  % (14880)Refutation not found, incomplete strategy% (14880)------------------------------
% 1.82/0.63  % (14880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.63  % (14880)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.63  
% 1.82/0.63  % (14880)Memory used [KB]: 1663
% 1.82/0.63  % (14880)Time elapsed: 0.193 s
% 1.82/0.63  % (14880)------------------------------
% 1.82/0.63  % (14880)------------------------------
% 1.82/0.63  % (14861)Refutation not found, incomplete strategy% (14861)------------------------------
% 1.82/0.63  % (14861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.63  % (14861)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.63  
% 1.82/0.63  % (14861)Memory used [KB]: 10746
% 1.82/0.63  % (14861)Time elapsed: 0.129 s
% 1.82/0.63  % (14861)------------------------------
% 1.82/0.63  % (14861)------------------------------
% 1.82/0.63  % (14879)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.82/0.63  % (14872)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.82/0.63  % (14871)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.19/0.63  % (14869)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.19/0.63  % (14876)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.19/0.63  % (14869)Refutation not found, incomplete strategy% (14869)------------------------------
% 2.19/0.63  % (14869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.63  % (14869)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.63  
% 2.19/0.63  % (14869)Memory used [KB]: 1791
% 2.19/0.63  % (14869)Time elapsed: 0.205 s
% 2.19/0.63  % (14869)------------------------------
% 2.19/0.63  % (14869)------------------------------
% 2.19/0.64  % (14864)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.19/0.64  % (14858)Refutation found. Thanks to Tanya!
% 2.19/0.64  % SZS status Theorem for theBenchmark
% 2.19/0.64  % SZS output start Proof for theBenchmark
% 2.19/0.64  % (14863)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.19/0.64  fof(f556,plain,(
% 2.19/0.64    $false),
% 2.19/0.64    inference(subsumption_resolution,[],[f555,f49])).
% 2.19/0.64  fof(f49,plain,(
% 2.19/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f2])).
% 2.19/0.64  fof(f2,axiom,(
% 2.19/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.19/0.64  fof(f555,plain,(
% 2.19/0.64    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 2.19/0.64    inference(forward_demodulation,[],[f527,f50])).
% 2.19/0.64  fof(f50,plain,(
% 2.19/0.64    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f12])).
% 2.19/0.64  fof(f12,axiom,(
% 2.19/0.64    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 2.19/0.64  fof(f527,plain,(
% 2.19/0.64    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 2.19/0.64    inference(backward_demodulation,[],[f114,f517])).
% 2.19/0.64  fof(f517,plain,(
% 2.19/0.64    k1_xboole_0 = sK3),
% 2.19/0.64    inference(subsumption_resolution,[],[f516,f49])).
% 2.19/0.64  fof(f516,plain,(
% 2.19/0.64    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3),
% 2.19/0.64    inference(forward_demodulation,[],[f515,f81])).
% 2.19/0.64  fof(f81,plain,(
% 2.19/0.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.19/0.64    inference(equality_resolution,[],[f65])).
% 2.19/0.64  fof(f65,plain,(
% 2.19/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.19/0.64    inference(cnf_transformation,[],[f42])).
% 2.19/0.64  fof(f42,plain,(
% 2.19/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.19/0.64    inference(flattening,[],[f41])).
% 2.19/0.64  fof(f41,plain,(
% 2.19/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.19/0.64    inference(nnf_transformation,[],[f7])).
% 2.19/0.64  fof(f7,axiom,(
% 2.19/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.19/0.64  fof(f515,plain,(
% 2.19/0.64    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | k1_xboole_0 = sK3),
% 2.19/0.64    inference(forward_demodulation,[],[f514,f488])).
% 2.19/0.64  fof(f488,plain,(
% 2.19/0.64    k1_xboole_0 = k1_relat_1(sK3)),
% 2.19/0.64    inference(subsumption_resolution,[],[f475,f97])).
% 2.19/0.64  fof(f97,plain,(
% 2.19/0.64    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k2_relat_1(sK3))) )),
% 2.19/0.64    inference(resolution,[],[f93,f53])).
% 2.19/0.64  fof(f53,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 2.19/0.64    inference(cnf_transformation,[],[f23])).
% 2.19/0.64  fof(f23,plain,(
% 2.19/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.19/0.64    inference(ennf_transformation,[],[f11])).
% 2.19/0.64  fof(f11,axiom,(
% 2.19/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 2.19/0.64  fof(f93,plain,(
% 2.19/0.64    v1_relat_1(sK3)),
% 2.19/0.64    inference(resolution,[],[f69,f46])).
% 2.19/0.64  fof(f46,plain,(
% 2.19/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.19/0.64    inference(cnf_transformation,[],[f35])).
% 2.19/0.64  fof(f35,plain,(
% 2.19/0.64    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.19/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f34])).
% 2.19/0.64  fof(f34,plain,(
% 2.19/0.64    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.19/0.64    introduced(choice_axiom,[])).
% 2.19/0.64  fof(f22,plain,(
% 2.19/0.64    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.19/0.64    inference(flattening,[],[f21])).
% 2.19/0.64  fof(f21,plain,(
% 2.19/0.64    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.19/0.64    inference(ennf_transformation,[],[f20])).
% 2.19/0.64  fof(f20,plain,(
% 2.19/0.64    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.19/0.64    inference(pure_predicate_removal,[],[f19])).
% 2.19/0.64  fof(f19,negated_conjecture,(
% 2.19/0.64    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.19/0.64    inference(negated_conjecture,[],[f18])).
% 2.19/0.64  fof(f18,conjecture,(
% 2.19/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 2.19/0.64  fof(f69,plain,(
% 2.19/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f30])).
% 2.19/0.64  fof(f30,plain,(
% 2.19/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.64    inference(ennf_transformation,[],[f14])).
% 2.19/0.64  fof(f14,axiom,(
% 2.19/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.19/0.64  fof(f475,plain,(
% 2.19/0.64    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.19/0.64    inference(superposition,[],[f114,f312])).
% 2.19/0.64  fof(f312,plain,(
% 2.19/0.64    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.19/0.64    inference(equality_resolution,[],[f216])).
% 2.19/0.64  fof(f216,plain,(
% 2.19/0.64    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X1)) | k1_xboole_0 = k1_relat_1(sK3)) )),
% 2.19/0.64    inference(superposition,[],[f118,f159])).
% 2.19/0.64  fof(f159,plain,(
% 2.19/0.64    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.19/0.64    inference(resolution,[],[f125,f127])).
% 2.19/0.64  fof(f127,plain,(
% 2.19/0.64    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.19/0.64    inference(subsumption_resolution,[],[f126,f93])).
% 2.19/0.64  fof(f126,plain,(
% 2.19/0.64    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3)),
% 2.19/0.64    inference(resolution,[],[f103,f54])).
% 2.19/0.64  fof(f54,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f36])).
% 2.19/0.64  fof(f36,plain,(
% 2.19/0.64    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.19/0.64    inference(nnf_transformation,[],[f24])).
% 2.19/0.64  fof(f24,plain,(
% 2.19/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.19/0.64    inference(ennf_transformation,[],[f9])).
% 2.19/0.64  fof(f9,axiom,(
% 2.19/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.19/0.64  fof(f103,plain,(
% 2.19/0.64    v4_relat_1(sK3,k1_tarski(sK0))),
% 2.19/0.64    inference(resolution,[],[f70,f46])).
% 2.19/0.64  fof(f70,plain,(
% 2.19/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f31])).
% 2.19/0.64  fof(f31,plain,(
% 2.19/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.64    inference(ennf_transformation,[],[f15])).
% 2.19/0.64  fof(f15,axiom,(
% 2.19/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.19/0.64  fof(f125,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_xboole_0 = X1) )),
% 2.19/0.64    inference(duplicate_literal_removal,[],[f124])).
% 2.19/0.64  fof(f124,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_tarski(X0) = X1 | k1_xboole_0 = X1 | k1_tarski(X0) = X1) )),
% 2.19/0.64    inference(superposition,[],[f72,f51])).
% 2.19/0.64  fof(f51,plain,(
% 2.19/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f3])).
% 2.19/0.64  fof(f3,axiom,(
% 2.19/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.19/0.64  fof(f72,plain,(
% 2.19/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 2.19/0.64    inference(cnf_transformation,[],[f44])).
% 2.19/0.64  fof(f44,plain,(
% 2.19/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.19/0.64    inference(flattening,[],[f43])).
% 2.19/0.64  fof(f43,plain,(
% 2.19/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.19/0.64    inference(nnf_transformation,[],[f32])).
% 2.19/0.64  fof(f32,plain,(
% 2.19/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.19/0.64    inference(ennf_transformation,[],[f6])).
% 2.19/0.64  fof(f6,axiom,(
% 2.19/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 2.19/0.64  fof(f118,plain,(
% 2.19/0.64    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) )),
% 2.19/0.64    inference(subsumption_resolution,[],[f117,f93])).
% 2.19/0.64  fof(f117,plain,(
% 2.19/0.64    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 2.19/0.64    inference(resolution,[],[f58,f45])).
% 2.19/0.64  fof(f45,plain,(
% 2.19/0.64    v1_funct_1(sK3)),
% 2.19/0.64    inference(cnf_transformation,[],[f35])).
% 2.19/0.64  fof(f58,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f27])).
% 2.19/0.64  fof(f27,plain,(
% 2.19/0.64    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.19/0.64    inference(flattening,[],[f26])).
% 2.19/0.64  fof(f26,plain,(
% 2.19/0.64    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.19/0.64    inference(ennf_transformation,[],[f13])).
% 2.19/0.64  fof(f13,axiom,(
% 2.19/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 2.19/0.64  fof(f514,plain,(
% 2.19/0.64    k1_xboole_0 = sK3 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)),
% 2.19/0.64    inference(forward_demodulation,[],[f505,f81])).
% 2.19/0.64  fof(f505,plain,(
% 2.19/0.64    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)),
% 2.19/0.64    inference(backward_demodulation,[],[f306,f488])).
% 2.19/0.64  fof(f306,plain,(
% 2.19/0.64    sK3 = k2_zfmisc_1(k1_relat_1(sK3),sK1) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)),
% 2.19/0.64    inference(resolution,[],[f267,f61])).
% 2.19/0.64  fof(f61,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f39])).
% 2.19/0.64  fof(f39,plain,(
% 2.19/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.64    inference(flattening,[],[f38])).
% 2.19/0.64  fof(f38,plain,(
% 2.19/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.64    inference(nnf_transformation,[],[f1])).
% 2.19/0.64  fof(f1,axiom,(
% 2.19/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.19/0.64  fof(f267,plain,(
% 2.19/0.64    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1))),
% 2.19/0.64    inference(resolution,[],[f219,f62])).
% 2.19/0.64  fof(f62,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f40])).
% 2.19/0.64  fof(f40,plain,(
% 2.19/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.19/0.64    inference(nnf_transformation,[],[f8])).
% 2.19/0.64  fof(f8,axiom,(
% 2.19/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.19/0.64  fof(f219,plain,(
% 2.19/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 2.19/0.64    inference(resolution,[],[f180,f78])).
% 2.19/0.64  fof(f78,plain,(
% 2.19/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.19/0.64    inference(equality_resolution,[],[f60])).
% 2.19/0.64  fof(f60,plain,(
% 2.19/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.19/0.64    inference(cnf_transformation,[],[f39])).
% 2.19/0.64  fof(f180,plain,(
% 2.19/0.64    ( ! [X1] : (~r1_tarski(k1_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))) )),
% 2.19/0.64    inference(resolution,[],[f119,f116])).
% 2.19/0.64  fof(f116,plain,(
% 2.19/0.64    r1_tarski(k2_relat_1(sK3),sK1)),
% 2.19/0.64    inference(subsumption_resolution,[],[f115,f93])).
% 2.19/0.64  fof(f115,plain,(
% 2.19/0.64    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 2.19/0.64    inference(resolution,[],[f106,f56])).
% 2.19/0.64  fof(f56,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f37])).
% 2.19/0.64  fof(f37,plain,(
% 2.19/0.64    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.19/0.64    inference(nnf_transformation,[],[f25])).
% 2.19/0.64  fof(f25,plain,(
% 2.19/0.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.19/0.64    inference(ennf_transformation,[],[f10])).
% 2.19/0.64  fof(f10,axiom,(
% 2.19/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.19/0.64  fof(f106,plain,(
% 2.19/0.64    v5_relat_1(sK3,sK1)),
% 2.19/0.64    inference(resolution,[],[f71,f46])).
% 2.19/0.64  fof(f71,plain,(
% 2.19/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f31])).
% 2.19/0.64  fof(f119,plain,(
% 2.19/0.64    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),X0) | ~r1_tarski(k1_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.19/0.64    inference(resolution,[],[f68,f93])).
% 2.19/0.64  fof(f68,plain,(
% 2.19/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.64    inference(cnf_transformation,[],[f29])).
% 2.19/0.64  fof(f29,plain,(
% 2.19/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.19/0.64    inference(flattening,[],[f28])).
% 2.19/0.64  fof(f28,plain,(
% 2.19/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.19/0.64    inference(ennf_transformation,[],[f17])).
% 2.19/0.64  fof(f17,axiom,(
% 2.19/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 2.19/0.64  fof(f114,plain,(
% 2.19/0.64    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.19/0.64    inference(backward_demodulation,[],[f48,f111])).
% 2.19/0.64  fof(f111,plain,(
% 2.19/0.64    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k1_tarski(sK0),sK1,sK3,X0)) )),
% 2.19/0.64    inference(resolution,[],[f77,f46])).
% 2.19/0.64  fof(f77,plain,(
% 2.19/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 2.19/0.64    inference(cnf_transformation,[],[f33])).
% 2.19/0.64  fof(f33,plain,(
% 2.19/0.64    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.64    inference(ennf_transformation,[],[f16])).
% 2.19/0.64  fof(f16,axiom,(
% 2.19/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.19/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.19/0.64  fof(f48,plain,(
% 2.19/0.64    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.19/0.64    inference(cnf_transformation,[],[f35])).
% 2.19/0.64  % SZS output end Proof for theBenchmark
% 2.19/0.64  % (14858)------------------------------
% 2.19/0.64  % (14858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.64  % (14858)Termination reason: Refutation
% 2.19/0.64  
% 2.19/0.64  % (14858)Memory used [KB]: 2046
% 2.19/0.64  % (14858)Time elapsed: 0.218 s
% 2.19/0.64  % (14858)------------------------------
% 2.19/0.64  % (14858)------------------------------
% 2.19/0.64  % (14850)Success in time 0.277 s
%------------------------------------------------------------------------------

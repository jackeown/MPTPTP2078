%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:42 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 734 expanded)
%              Number of leaves         :   23 ( 171 expanded)
%              Depth                    :   23
%              Number of atoms          :  433 (2538 expanded)
%              Number of equality atoms :  188 ( 777 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1540,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1539,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1539,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1259,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f1259,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1174,f1182])).

fof(f1182,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f1181,f75])).

fof(f1181,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f1180,f132])).

fof(f132,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1180,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f1179,f1126])).

fof(f1126,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1096,f519])).

fof(f519,plain,(
    ! [X6] : r1_tarski(k9_relat_1(sK3,X6),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f293,f514])).

fof(f514,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(superposition,[],[f294,f474])).

fof(f474,plain,(
    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f472,f275])).

fof(f275,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f152,f70])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f57])).

fof(f57,plain,
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

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f152,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_relat_1(X1) ) ),
    inference(resolution,[],[f82,f87])).

fof(f87,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f472,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f412,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f412,plain,(
    v4_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f296,f129])).

fof(f129,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
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

fof(f296,plain,(
    ! [X9] :
      ( ~ r1_tarski(k1_relat_1(sK3),X9)
      | v4_relat_1(sK3,X9) ) ),
    inference(resolution,[],[f275,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f294,plain,(
    ! [X7] : k9_relat_1(sK3,X7) = k2_relat_1(k7_relat_1(sK3,X7)) ),
    inference(resolution,[],[f275,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f293,plain,(
    ! [X6] : r1_tarski(k9_relat_1(sK3,X6),k9_relat_1(sK3,k1_relat_1(sK3))) ),
    inference(resolution,[],[f275,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

fof(f1096,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f218,f770])).

fof(f770,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(equality_resolution,[],[f500])).

fof(f500,plain,(
    ! [X2] :
      ( k1_tarski(X2) != k1_tarski(sK0)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X2))
      | k1_xboole_0 = k1_relat_1(sK3) ) ),
    inference(superposition,[],[f291,f380])).

fof(f380,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f356,f288])).

fof(f288,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(resolution,[],[f275,f210])).

fof(f210,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(resolution,[],[f185,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f185,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f109,f70])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f356,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tarski(X0))
      | k1_tarski(X0) = X1
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tarski(X0))
      | k1_tarski(X0) = X1
      | k1_tarski(X0) = X1
      | k1_tarski(X0) = X1
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f244,f78])).

fof(f78,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_tarski(X0,X1))
      | k1_tarski(X0) = X2
      | k2_tarski(X0,X1) = X2
      | k1_tarski(X1) = X2
      | k1_xboole_0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X2
      | ~ r1_tarski(X2,k2_tarski(X0,X1))
      | k2_tarski(X0,X1) = X2
      | k1_tarski(X1) = X2
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(forward_demodulation,[],[f242,f78])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_tarski(X0,X1))
      | k2_tarski(X0,X1) = X2
      | k2_tarski(X0,X0) = X2
      | k1_tarski(X1) = X2
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_tarski(X0,X1))
      | k2_tarski(X0,X1) = X2
      | k2_tarski(X0,X1) = X2
      | k2_tarski(X0,X0) = X2
      | k1_tarski(X1) = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2
      | k2_tarski(X0,X1) = X2 ) ),
    inference(superposition,[],[f114,f88])).

fof(f88,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | k1_enumset1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(flattening,[],[f67])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f291,plain,(
    ! [X3] :
      ( k1_tarski(X3) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X3)) ) ),
    inference(resolution,[],[f275,f224])).

fof(f224,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))
      | k1_tarski(X0) != k1_relat_1(sK3) ) ),
    inference(resolution,[],[f97,f69])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f218,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f72,f213])).

fof(f213,plain,(
    ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f113,f70])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f1179,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) ),
    inference(forward_demodulation,[],[f1156,f132])).

fof(f1156,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) ),
    inference(backward_demodulation,[],[f718,f1126])).

fof(f718,plain,
    ( sK3 = k2_zfmisc_1(k1_relat_1(sK3),sK1)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3) ),
    inference(resolution,[],[f491,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f491,plain,(
    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1)) ),
    inference(resolution,[],[f420,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f420,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    inference(resolution,[],[f289,f285])).

fof(f285,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(resolution,[],[f275,f195])).

fof(f195,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(resolution,[],[f190,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f190,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f110,f70])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f289,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1))) ) ),
    inference(resolution,[],[f275,f211])).

fof(f211,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | ~ r1_tarski(k2_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f96,f69])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_1(X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1174,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f218,f1170])).

fof(f1170,plain,(
    ! [X2] : k1_xboole_0 = k1_funct_1(sK3,X2) ),
    inference(subsumption_resolution,[],[f1145,f75])).

fof(f1145,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | k1_xboole_0 = k1_funct_1(sK3,X2) ) ),
    inference(backward_demodulation,[],[f418,f1126])).

fof(f418,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(sK3),X2)
      | k1_xboole_0 = k1_funct_1(sK3,X2) ) ),
    inference(resolution,[],[f286,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f286,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK3))
      | k1_xboole_0 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f275,f205])).

fof(f205,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | k1_xboole_0 = k1_funct_1(sK3,X0)
      | r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f126,f69])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (20698)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (20706)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (20702)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.50  % (20690)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (20702)Refutation not found, incomplete strategy% (20702)------------------------------
% 0.21/0.50  % (20702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20698)Refutation not found, incomplete strategy% (20698)------------------------------
% 0.21/0.51  % (20698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20695)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (20698)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20698)Memory used [KB]: 1791
% 0.21/0.51  % (20698)Time elapsed: 0.060 s
% 0.21/0.51  % (20698)------------------------------
% 0.21/0.51  % (20698)------------------------------
% 0.21/0.51  % (20688)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (20710)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (20694)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (20693)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (20702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20702)Memory used [KB]: 1791
% 0.21/0.51  % (20702)Time elapsed: 0.105 s
% 0.21/0.51  % (20702)------------------------------
% 0.21/0.51  % (20702)------------------------------
% 0.21/0.51  % (20692)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (20707)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (20684)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (20703)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (20687)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (20689)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (20696)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (20686)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (20711)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (20708)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (20711)Refutation not found, incomplete strategy% (20711)------------------------------
% 0.21/0.53  % (20711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20711)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20711)Memory used [KB]: 6268
% 0.21/0.53  % (20711)Time elapsed: 0.131 s
% 0.21/0.53  % (20711)------------------------------
% 0.21/0.53  % (20711)------------------------------
% 0.21/0.53  % (20710)Refutation not found, incomplete strategy% (20710)------------------------------
% 0.21/0.53  % (20710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20691)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (20685)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (20710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20710)Memory used [KB]: 6524
% 0.21/0.53  % (20710)Time elapsed: 0.134 s
% 0.21/0.53  % (20710)------------------------------
% 0.21/0.53  % (20710)------------------------------
% 0.21/0.53  % (20712)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (20685)Refutation not found, incomplete strategy% (20685)------------------------------
% 0.21/0.53  % (20685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20685)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20685)Memory used [KB]: 1663
% 0.21/0.53  % (20685)Time elapsed: 0.136 s
% 0.21/0.53  % (20685)------------------------------
% 0.21/0.53  % (20685)------------------------------
% 0.21/0.53  % (20705)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (20712)Refutation not found, incomplete strategy% (20712)------------------------------
% 0.21/0.54  % (20712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20712)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20712)Memory used [KB]: 10874
% 0.21/0.54  % (20712)Time elapsed: 0.141 s
% 0.21/0.54  % (20712)------------------------------
% 0.21/0.54  % (20712)------------------------------
% 0.21/0.54  % (20709)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (20694)Refutation not found, incomplete strategy% (20694)------------------------------
% 0.21/0.54  % (20694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20694)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20694)Memory used [KB]: 10874
% 0.21/0.54  % (20694)Time elapsed: 0.138 s
% 0.21/0.54  % (20694)------------------------------
% 0.21/0.54  % (20694)------------------------------
% 0.21/0.54  % (20704)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (20713)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (20713)Refutation not found, incomplete strategy% (20713)------------------------------
% 0.21/0.54  % (20713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20713)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20713)Memory used [KB]: 1663
% 0.21/0.54  % (20713)Time elapsed: 0.150 s
% 0.21/0.54  % (20713)------------------------------
% 0.21/0.54  % (20713)------------------------------
% 0.21/0.54  % (20700)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (20700)Refutation not found, incomplete strategy% (20700)------------------------------
% 0.21/0.54  % (20700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20700)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20700)Memory used [KB]: 10746
% 0.21/0.54  % (20700)Time elapsed: 0.149 s
% 0.21/0.54  % (20700)------------------------------
% 0.21/0.54  % (20700)------------------------------
% 0.21/0.55  % (20697)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (20701)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (20699)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.01/0.63  % (20691)Refutation found. Thanks to Tanya!
% 2.01/0.63  % SZS status Theorem for theBenchmark
% 2.01/0.63  % SZS output start Proof for theBenchmark
% 2.01/0.63  fof(f1540,plain,(
% 2.01/0.63    $false),
% 2.01/0.63    inference(subsumption_resolution,[],[f1539,f75])).
% 2.01/0.63  fof(f75,plain,(
% 2.01/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f2])).
% 2.01/0.63  fof(f2,axiom,(
% 2.01/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.01/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.01/0.63  fof(f1539,plain,(
% 2.01/0.63    ~r1_tarski(k1_xboole_0,k1_tarski(k1_xboole_0))),
% 2.01/0.63    inference(forward_demodulation,[],[f1259,f77])).
% 2.01/0.63  fof(f77,plain,(
% 2.01/0.63    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f21])).
% 2.01/0.63  fof(f21,axiom,(
% 2.01/0.63    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.01/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 2.01/0.63  fof(f1259,plain,(
% 2.01/0.63    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_xboole_0))),
% 2.01/0.63    inference(backward_demodulation,[],[f1174,f1182])).
% 2.01/0.63  fof(f1182,plain,(
% 2.01/0.63    k1_xboole_0 = sK3),
% 2.01/0.63    inference(subsumption_resolution,[],[f1181,f75])).
% 2.01/0.63  fof(f1181,plain,(
% 2.01/0.63    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3),
% 2.01/0.63    inference(forward_demodulation,[],[f1180,f132])).
% 2.01/0.63  fof(f132,plain,(
% 2.01/0.63    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.01/0.63    inference(equality_resolution,[],[f105])).
% 2.01/0.63  fof(f105,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.01/0.63    inference(cnf_transformation,[],[f66])).
% 2.01/0.63  fof(f66,plain,(
% 2.01/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.01/0.63    inference(flattening,[],[f65])).
% 2.01/0.63  fof(f65,plain,(
% 2.01/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.01/0.63    inference(nnf_transformation,[],[f10])).
% 2.01/0.63  fof(f10,axiom,(
% 2.01/0.63    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.01/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.01/0.63  fof(f1180,plain,(
% 2.01/0.63    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | k1_xboole_0 = sK3),
% 2.01/0.63    inference(forward_demodulation,[],[f1179,f1126])).
% 2.01/0.63  fof(f1126,plain,(
% 2.01/0.63    k1_xboole_0 = k1_relat_1(sK3)),
% 2.01/0.63    inference(subsumption_resolution,[],[f1096,f519])).
% 2.01/0.63  fof(f519,plain,(
% 2.01/0.63    ( ! [X6] : (r1_tarski(k9_relat_1(sK3,X6),k2_relat_1(sK3))) )),
% 2.01/0.63    inference(backward_demodulation,[],[f293,f514])).
% 2.01/0.63  fof(f514,plain,(
% 2.01/0.63    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3))),
% 2.01/0.63    inference(superposition,[],[f294,f474])).
% 2.01/0.63  fof(f474,plain,(
% 2.01/0.63    sK3 = k7_relat_1(sK3,k1_relat_1(sK3))),
% 2.01/0.63    inference(subsumption_resolution,[],[f472,f275])).
% 2.01/0.63  fof(f275,plain,(
% 2.01/0.63    v1_relat_1(sK3)),
% 2.01/0.63    inference(resolution,[],[f152,f70])).
% 2.01/0.63  fof(f70,plain,(
% 2.01/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.01/0.63    inference(cnf_transformation,[],[f58])).
% 2.01/0.64  fof(f58,plain,(
% 2.01/0.64    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.01/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f57])).
% 2.01/0.64  fof(f57,plain,(
% 2.01/0.64    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.01/0.64    introduced(choice_axiom,[])).
% 2.01/0.64  fof(f37,plain,(
% 2.01/0.64    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.01/0.64    inference(flattening,[],[f36])).
% 2.01/0.64  fof(f36,plain,(
% 2.01/0.64    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.01/0.64    inference(ennf_transformation,[],[f34])).
% 2.01/0.64  fof(f34,plain,(
% 2.01/0.64    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.01/0.64    inference(pure_predicate_removal,[],[f32])).
% 2.01/0.64  fof(f32,negated_conjecture,(
% 2.01/0.64    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.01/0.64    inference(negated_conjecture,[],[f31])).
% 2.01/0.64  fof(f31,conjecture,(
% 2.01/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 2.01/0.64  fof(f152,plain,(
% 2.01/0.64    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_relat_1(X1)) )),
% 2.01/0.64    inference(resolution,[],[f82,f87])).
% 2.01/0.64  fof(f87,plain,(
% 2.01/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f18])).
% 2.01/0.64  fof(f18,axiom,(
% 2.01/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.01/0.64  fof(f82,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f38])).
% 2.01/0.64  fof(f38,plain,(
% 2.01/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.01/0.64    inference(ennf_transformation,[],[f15])).
% 2.01/0.64  fof(f15,axiom,(
% 2.01/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.01/0.64  fof(f472,plain,(
% 2.01/0.64    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 2.01/0.64    inference(resolution,[],[f412,f98])).
% 2.01/0.64  fof(f98,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f50])).
% 2.01/0.64  fof(f50,plain,(
% 2.01/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(flattening,[],[f49])).
% 2.01/0.64  fof(f49,plain,(
% 2.01/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.01/0.64    inference(ennf_transformation,[],[f22])).
% 2.01/0.64  fof(f22,axiom,(
% 2.01/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.01/0.64  fof(f412,plain,(
% 2.01/0.64    v4_relat_1(sK3,k1_relat_1(sK3))),
% 2.01/0.64    inference(resolution,[],[f296,f129])).
% 2.01/0.64  fof(f129,plain,(
% 2.01/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.01/0.64    inference(equality_resolution,[],[f100])).
% 2.01/0.64  fof(f100,plain,(
% 2.01/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.01/0.64    inference(cnf_transformation,[],[f63])).
% 2.01/0.64  fof(f63,plain,(
% 2.01/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.64    inference(flattening,[],[f62])).
% 2.01/0.64  fof(f62,plain,(
% 2.01/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.64    inference(nnf_transformation,[],[f1])).
% 2.01/0.64  fof(f1,axiom,(
% 2.01/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.01/0.64  fof(f296,plain,(
% 2.01/0.64    ( ! [X9] : (~r1_tarski(k1_relat_1(sK3),X9) | v4_relat_1(sK3,X9)) )),
% 2.01/0.64    inference(resolution,[],[f275,f92])).
% 2.01/0.64  fof(f92,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f60])).
% 2.01/0.64  fof(f60,plain,(
% 2.01/0.64    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(nnf_transformation,[],[f43])).
% 2.01/0.64  fof(f43,plain,(
% 2.01/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f16])).
% 2.01/0.64  fof(f16,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.01/0.64  fof(f294,plain,(
% 2.01/0.64    ( ! [X7] : (k9_relat_1(sK3,X7) = k2_relat_1(k7_relat_1(sK3,X7))) )),
% 2.01/0.64    inference(resolution,[],[f275,f89])).
% 2.01/0.64  fof(f89,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f41])).
% 2.01/0.64  fof(f41,plain,(
% 2.01/0.64    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f20])).
% 2.01/0.64  fof(f20,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.01/0.64  fof(f293,plain,(
% 2.01/0.64    ( ! [X6] : (r1_tarski(k9_relat_1(sK3,X6),k9_relat_1(sK3,k1_relat_1(sK3)))) )),
% 2.01/0.64    inference(resolution,[],[f275,f90])).
% 2.01/0.64  fof(f90,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f42])).
% 2.01/0.64  fof(f42,plain,(
% 2.01/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f19])).
% 2.01/0.64  fof(f19,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).
% 2.01/0.64  fof(f1096,plain,(
% 2.01/0.64    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.01/0.64    inference(superposition,[],[f218,f770])).
% 2.01/0.64  fof(f770,plain,(
% 2.01/0.64    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.01/0.64    inference(equality_resolution,[],[f500])).
% 2.01/0.64  fof(f500,plain,(
% 2.01/0.64    ( ! [X2] : (k1_tarski(X2) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X2)) | k1_xboole_0 = k1_relat_1(sK3)) )),
% 2.01/0.64    inference(superposition,[],[f291,f380])).
% 2.01/0.64  fof(f380,plain,(
% 2.01/0.64    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 2.01/0.64    inference(resolution,[],[f356,f288])).
% 2.01/0.64  fof(f288,plain,(
% 2.01/0.64    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.01/0.64    inference(resolution,[],[f275,f210])).
% 2.01/0.64  fof(f210,plain,(
% 2.01/0.64    ~v1_relat_1(sK3) | r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.01/0.64    inference(resolution,[],[f185,f91])).
% 2.01/0.64  fof(f91,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f60])).
% 2.01/0.64  fof(f185,plain,(
% 2.01/0.64    v4_relat_1(sK3,k1_tarski(sK0))),
% 2.01/0.64    inference(resolution,[],[f109,f70])).
% 2.01/0.64  fof(f109,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f52])).
% 2.01/0.64  fof(f52,plain,(
% 2.01/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.64    inference(ennf_transformation,[],[f28])).
% 2.01/0.64  fof(f28,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.01/0.64  fof(f356,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_xboole_0 = X1) )),
% 2.01/0.64    inference(duplicate_literal_removal,[],[f355])).
% 2.01/0.64  fof(f355,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(X1,k1_tarski(X0)) | k1_tarski(X0) = X1 | k1_tarski(X0) = X1 | k1_tarski(X0) = X1 | k1_xboole_0 = X1) )),
% 2.01/0.64    inference(superposition,[],[f244,f78])).
% 2.01/0.64  fof(f78,plain,(
% 2.01/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f3])).
% 2.01/0.64  fof(f3,axiom,(
% 2.01/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.01/0.64  fof(f244,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_tarski(X0,X1)) | k1_tarski(X0) = X2 | k2_tarski(X0,X1) = X2 | k1_tarski(X1) = X2 | k1_xboole_0 = X2) )),
% 2.01/0.64    inference(duplicate_literal_removal,[],[f243])).
% 2.01/0.64  fof(f243,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (k1_tarski(X0) = X2 | ~r1_tarski(X2,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = X2 | k1_tarski(X1) = X2 | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 2.01/0.64    inference(forward_demodulation,[],[f242,f78])).
% 2.01/0.64  fof(f242,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = X2 | k2_tarski(X0,X0) = X2 | k1_tarski(X1) = X2 | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 2.01/0.64    inference(duplicate_literal_removal,[],[f241])).
% 2.01/0.64  fof(f241,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_tarski(X0,X1)) | k2_tarski(X0,X1) = X2 | k2_tarski(X0,X1) = X2 | k2_tarski(X0,X0) = X2 | k1_tarski(X1) = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) = X2 | k1_xboole_0 = X2 | k2_tarski(X0,X1) = X2) )),
% 2.01/0.64    inference(superposition,[],[f114,f88])).
% 2.01/0.64  fof(f88,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f4])).
% 2.01/0.64  fof(f4,axiom,(
% 2.01/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.01/0.64  fof(f114,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | k1_enumset1(X0,X1,X2) = X3) )),
% 2.01/0.64    inference(cnf_transformation,[],[f68])).
% 2.01/0.64  fof(f68,plain,(
% 2.01/0.64    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.01/0.64    inference(flattening,[],[f67])).
% 2.01/0.64  fof(f67,plain,(
% 2.01/0.64    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.01/0.64    inference(nnf_transformation,[],[f56])).
% 2.01/0.64  fof(f56,plain,(
% 2.01/0.64    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.01/0.64    inference(ennf_transformation,[],[f11])).
% 2.01/0.64  fof(f11,axiom,(
% 2.01/0.64    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 2.01/0.64  fof(f291,plain,(
% 2.01/0.64    ( ! [X3] : (k1_tarski(X3) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X3))) )),
% 2.01/0.64    inference(resolution,[],[f275,f224])).
% 2.01/0.64  fof(f224,plain,(
% 2.01/0.64    ( ! [X0] : (~v1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) | k1_tarski(X0) != k1_relat_1(sK3)) )),
% 2.01/0.64    inference(resolution,[],[f97,f69])).
% 2.01/0.64  fof(f69,plain,(
% 2.01/0.64    v1_funct_1(sK3)),
% 2.01/0.64    inference(cnf_transformation,[],[f58])).
% 2.01/0.64  fof(f97,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f48])).
% 2.01/0.64  fof(f48,plain,(
% 2.01/0.64    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(flattening,[],[f47])).
% 2.01/0.64  fof(f47,plain,(
% 2.01/0.64    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.01/0.64    inference(ennf_transformation,[],[f25])).
% 2.01/0.64  fof(f25,axiom,(
% 2.01/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 2.01/0.64  fof(f218,plain,(
% 2.01/0.64    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.01/0.64    inference(backward_demodulation,[],[f72,f213])).
% 2.01/0.64  fof(f213,plain,(
% 2.01/0.64    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 2.01/0.64    inference(resolution,[],[f113,f70])).
% 2.01/0.64  fof(f113,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f55])).
% 2.01/0.64  fof(f55,plain,(
% 2.01/0.64    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.64    inference(ennf_transformation,[],[f29])).
% 2.01/0.64  fof(f29,axiom,(
% 2.01/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.01/0.64  fof(f72,plain,(
% 2.01/0.64    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.01/0.64    inference(cnf_transformation,[],[f58])).
% 2.01/0.64  fof(f1179,plain,(
% 2.01/0.64    k1_xboole_0 = sK3 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)),
% 2.01/0.64    inference(forward_demodulation,[],[f1156,f132])).
% 2.01/0.64  fof(f1156,plain,(
% 2.01/0.64    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)),
% 2.01/0.64    inference(backward_demodulation,[],[f718,f1126])).
% 2.01/0.64  fof(f718,plain,(
% 2.01/0.64    sK3 = k2_zfmisc_1(k1_relat_1(sK3),sK1) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),sK1),sK3)),
% 2.01/0.64    inference(resolution,[],[f491,f101])).
% 2.01/0.64  fof(f101,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f63])).
% 2.01/0.64  fof(f491,plain,(
% 2.01/0.64    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1))),
% 2.01/0.64    inference(resolution,[],[f420,f102])).
% 2.01/0.64  fof(f102,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f64])).
% 2.01/0.64  fof(f64,plain,(
% 2.01/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.01/0.64    inference(nnf_transformation,[],[f13])).
% 2.01/0.64  fof(f13,axiom,(
% 2.01/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.01/0.64  fof(f420,plain,(
% 2.01/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 2.01/0.64    inference(resolution,[],[f289,f285])).
% 2.01/0.64  fof(f285,plain,(
% 2.01/0.64    r1_tarski(k2_relat_1(sK3),sK1)),
% 2.01/0.64    inference(resolution,[],[f275,f195])).
% 2.01/0.64  fof(f195,plain,(
% 2.01/0.64    ~v1_relat_1(sK3) | r1_tarski(k2_relat_1(sK3),sK1)),
% 2.01/0.64    inference(resolution,[],[f190,f93])).
% 2.01/0.64  fof(f93,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f61])).
% 2.01/0.64  fof(f61,plain,(
% 2.01/0.64    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(nnf_transformation,[],[f44])).
% 2.01/0.64  fof(f44,plain,(
% 2.01/0.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f17])).
% 2.01/0.64  fof(f17,axiom,(
% 2.01/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.01/0.64  fof(f190,plain,(
% 2.01/0.64    v5_relat_1(sK3,sK1)),
% 2.01/0.64    inference(resolution,[],[f110,f70])).
% 2.01/0.64  fof(f110,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f52])).
% 2.01/0.64  fof(f289,plain,(
% 2.01/0.64    ( ! [X1] : (~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X1)))) )),
% 2.01/0.64    inference(resolution,[],[f275,f211])).
% 2.01/0.64  fof(f211,plain,(
% 2.01/0.64    ( ! [X0] : (~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~r1_tarski(k2_relat_1(sK3),X0)) )),
% 2.01/0.64    inference(resolution,[],[f96,f69])).
% 2.01/0.64  fof(f96,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f46])).
% 2.01/0.64  fof(f46,plain,(
% 2.01/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.01/0.64    inference(flattening,[],[f45])).
% 2.01/0.64  fof(f45,plain,(
% 2.01/0.64    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.01/0.64    inference(ennf_transformation,[],[f33])).
% 2.01/0.64  fof(f33,plain,(
% 2.01/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1))))),
% 2.01/0.64    inference(pure_predicate_removal,[],[f30])).
% 2.01/0.64  fof(f30,axiom,(
% 2.01/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 2.01/0.64  fof(f1174,plain,(
% 2.01/0.64    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_xboole_0))),
% 2.01/0.64    inference(backward_demodulation,[],[f218,f1170])).
% 2.01/0.64  fof(f1170,plain,(
% 2.01/0.64    ( ! [X2] : (k1_xboole_0 = k1_funct_1(sK3,X2)) )),
% 2.01/0.64    inference(subsumption_resolution,[],[f1145,f75])).
% 2.01/0.64  fof(f1145,plain,(
% 2.01/0.64    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | k1_xboole_0 = k1_funct_1(sK3,X2)) )),
% 2.01/0.64    inference(backward_demodulation,[],[f418,f1126])).
% 2.01/0.64  fof(f418,plain,(
% 2.01/0.64    ( ! [X2] : (~r1_tarski(k1_relat_1(sK3),X2) | k1_xboole_0 = k1_funct_1(sK3,X2)) )),
% 2.01/0.64    inference(resolution,[],[f286,f107])).
% 2.01/0.64  fof(f107,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f51])).
% 2.01/0.64  fof(f51,plain,(
% 2.01/0.64    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f27])).
% 2.01/0.64  fof(f27,axiom,(
% 2.01/0.64    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.01/0.64  fof(f286,plain,(
% 2.01/0.64    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK3)) | k1_xboole_0 = k1_funct_1(sK3,X0)) )),
% 2.01/0.64    inference(resolution,[],[f275,f205])).
% 2.01/0.64  fof(f205,plain,(
% 2.01/0.64    ( ! [X0] : (~v1_relat_1(sK3) | k1_xboole_0 = k1_funct_1(sK3,X0) | r2_hidden(X0,k1_relat_1(sK3))) )),
% 2.01/0.64    inference(resolution,[],[f126,f69])).
% 2.01/0.64  fof(f126,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.01/0.64    inference(equality_resolution,[],[f86])).
% 2.01/0.64  fof(f86,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f59])).
% 2.01/0.64  fof(f59,plain,(
% 2.01/0.64    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.64    inference(nnf_transformation,[],[f40])).
% 2.01/0.64  fof(f40,plain,(
% 2.01/0.64    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.64    inference(flattening,[],[f39])).
% 2.01/0.64  fof(f39,plain,(
% 2.01/0.64    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.64    inference(ennf_transformation,[],[f24])).
% 2.01/0.64  fof(f24,axiom,(
% 2.01/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.01/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 2.01/0.64  % SZS output end Proof for theBenchmark
% 2.01/0.64  % (20691)------------------------------
% 2.01/0.64  % (20691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (20691)Termination reason: Refutation
% 2.01/0.64  
% 2.01/0.64  % (20691)Memory used [KB]: 2686
% 2.01/0.64  % (20691)Time elapsed: 0.225 s
% 2.01/0.64  % (20691)------------------------------
% 2.01/0.64  % (20691)------------------------------
% 2.01/0.64  % (20683)Success in time 0.277 s
%------------------------------------------------------------------------------

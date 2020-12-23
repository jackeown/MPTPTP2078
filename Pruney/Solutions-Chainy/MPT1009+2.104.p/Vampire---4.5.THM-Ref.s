%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:41 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  115 (1586 expanded)
%              Number of leaves         :   15 ( 382 expanded)
%              Depth                    :   32
%              Number of atoms          :  317 (5843 expanded)
%              Number of equality atoms :   87 (1364 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f802,plain,(
    $false ),
    inference(subsumption_resolution,[],[f790,f106])).

fof(f106,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f790,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f492,f789])).

fof(f789,plain,(
    ! [X4] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X4) ),
    inference(subsumption_resolution,[],[f788,f124])).

fof(f124,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f64,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f788,plain,(
    ! [X4] :
      ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f784,f539])).

fof(f539,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f501,f179])).

fof(f179,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[],[f171,f107])).

fof(f171,plain,(
    ! [X0,X1] : v4_relat_1(k2_zfmisc_1(X0,X1),X0) ),
    inference(resolution,[],[f150,f103])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f88,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f501,plain,(
    ! [X0] :
      ( ~ v4_relat_1(k1_xboole_0,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(backward_demodulation,[],[f372,f482])).

fof(f482,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f481,f439])).

fof(f439,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(resolution,[],[f393,f103])).

fof(f393,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_relat_1(sK3),X10)
      | r1_tarski(sK3,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f392,f108])).

fof(f108,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f392,plain,(
    ! [X10] :
      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X10))
      | ~ r1_tarski(k2_relat_1(sK3),X10) ) ),
    inference(subsumption_resolution,[],[f391,f130])).

fof(f130,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f128,f64])).

fof(f128,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f391,plain,(
    ! [X10] :
      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X10))
      | ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X10) ) ),
    inference(subsumption_resolution,[],[f369,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f369,plain,(
    ! [X10] :
      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X10))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ r1_tarski(k2_relat_1(sK3),X10) ) ),
    inference(superposition,[],[f185,f314])).

fof(f314,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f313,f149])).

fof(f149,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f88,f58])).

fof(f313,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f310])).

fof(f310,plain,(
    ! [X35] :
      ( k1_tarski(sK0) != k1_tarski(X35)
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v4_relat_1(sK3,k1_tarski(X35)) ) ),
    inference(subsumption_resolution,[],[f286,f130])).

fof(f286,plain,(
    ! [X35] :
      ( k1_tarski(sK0) != k1_tarski(X35)
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v4_relat_1(sK3,k1_tarski(X35))
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f199,f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) = k1_tarski(X3)
      | k1_xboole_0 = k1_relat_1(X2)
      | ~ v4_relat_1(X2,k1_tarski(X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f78,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f199,plain,(
    k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f198,f130])).

fof(f198,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f195,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f195,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f194,f130])).

fof(f194,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f189,f56])).

fof(f189,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f188,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f188,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(subsumption_resolution,[],[f187,f58])).

fof(f187,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(superposition,[],[f60,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f185,plain,(
    ! [X8,X9] :
      ( r1_tarski(X8,k2_zfmisc_1(k1_relat_1(X8),X9))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ r1_tarski(k2_relat_1(X8),X9) ) ),
    inference(resolution,[],[f73,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f481,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(resolution,[],[f452,f407])).

fof(f407,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ r1_tarski(sK3,k1_xboole_0) ) ),
    inference(resolution,[],[f372,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X0,X1)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f151,f82])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f88,f107])).

fof(f452,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f439,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f372,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f358,f130])).

fof(f358,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ v4_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f69,f314])).

fof(f784,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X4))
      | k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f147,f759])).

fof(f759,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f756,f124])).

fof(f756,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f532,f66])).

fof(f532,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f476,f482])).

fof(f476,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f471,f124])).

fof(f471,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f331,f223])).

fof(f223,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(superposition,[],[f215,f108])).

fof(f215,plain,(
    ! [X0,X1] : v5_relat_1(k2_zfmisc_1(X0,X1),X1) ),
    inference(resolution,[],[f154,f103])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f89,f82])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f331,plain,(
    ! [X7] :
      ( ~ v5_relat_1(X7,k1_tarski(k1_funct_1(sK3,sK0)))
      | k1_xboole_0 = k2_relat_1(X7)
      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(X7))
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f188,f163])).

fof(f163,plain,(
    ! [X4,X5] :
      ( k2_relat_1(X4) = k1_tarski(X5)
      | k1_xboole_0 = k2_relat_1(X4)
      | ~ v5_relat_1(X4,k1_tarski(X5))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f78,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f147,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(k2_relat_1(X6),k9_relat_1(X6,X7))
      | k2_relat_1(X6) = k9_relat_1(X6,X7)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f77,f66])).

fof(f492,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f188,f482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (6769)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (6776)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (6766)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (6771)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (6778)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (6783)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (6793)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (6770)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (6768)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (6772)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (6789)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (6781)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (6776)Refutation not found, incomplete strategy% (6776)------------------------------
% 0.21/0.54  % (6776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6793)Refutation not found, incomplete strategy% (6793)------------------------------
% 0.21/0.54  % (6793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6793)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6793)Memory used [KB]: 6268
% 0.21/0.54  % (6793)Time elapsed: 0.125 s
% 0.21/0.54  % (6793)------------------------------
% 0.21/0.54  % (6793)------------------------------
% 0.21/0.54  % (6776)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6776)Memory used [KB]: 10874
% 0.21/0.54  % (6776)Time elapsed: 0.126 s
% 0.21/0.54  % (6776)------------------------------
% 0.21/0.54  % (6776)------------------------------
% 0.21/0.55  % (6767)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (6777)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (6773)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (6767)Refutation not found, incomplete strategy% (6767)------------------------------
% 0.21/0.55  % (6767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6767)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6767)Memory used [KB]: 1663
% 0.21/0.55  % (6767)Time elapsed: 0.125 s
% 0.21/0.55  % (6767)------------------------------
% 0.21/0.55  % (6767)------------------------------
% 0.21/0.55  % (6790)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (6787)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (6794)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (6791)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (6780)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (6786)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (6780)Refutation not found, incomplete strategy% (6780)------------------------------
% 0.21/0.56  % (6780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6780)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6780)Memory used [KB]: 1791
% 0.21/0.56  % (6780)Time elapsed: 0.136 s
% 0.21/0.56  % (6780)------------------------------
% 0.21/0.56  % (6780)------------------------------
% 0.21/0.56  % (6795)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (6775)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (6795)Refutation not found, incomplete strategy% (6795)------------------------------
% 0.21/0.56  % (6795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6795)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6795)Memory used [KB]: 1663
% 0.21/0.56  % (6795)Time elapsed: 0.146 s
% 0.21/0.56  % (6795)------------------------------
% 0.21/0.56  % (6795)------------------------------
% 0.21/0.56  % (6788)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (6784)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (6782)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (6779)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (6782)Refutation not found, incomplete strategy% (6782)------------------------------
% 0.21/0.56  % (6782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6782)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6782)Memory used [KB]: 10746
% 0.21/0.56  % (6782)Time elapsed: 0.143 s
% 0.21/0.56  % (6782)------------------------------
% 0.21/0.56  % (6782)------------------------------
% 0.21/0.57  % (6790)Refutation not found, incomplete strategy% (6790)------------------------------
% 0.21/0.57  % (6790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (6790)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (6790)Memory used [KB]: 10746
% 0.21/0.57  % (6790)Time elapsed: 0.145 s
% 0.21/0.57  % (6790)------------------------------
% 0.21/0.57  % (6790)------------------------------
% 0.21/0.57  % (6794)Refutation not found, incomplete strategy% (6794)------------------------------
% 0.21/0.57  % (6794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (6794)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (6794)Memory used [KB]: 10874
% 0.21/0.57  % (6794)Time elapsed: 0.157 s
% 0.21/0.57  % (6794)------------------------------
% 0.21/0.57  % (6794)------------------------------
% 0.21/0.58  % (6774)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.58  % (6785)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.59  % (6792)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.93/0.62  % (6775)Refutation found. Thanks to Tanya!
% 1.93/0.62  % SZS status Theorem for theBenchmark
% 1.93/0.62  % SZS output start Proof for theBenchmark
% 1.93/0.62  fof(f802,plain,(
% 1.93/0.62    $false),
% 1.93/0.62    inference(subsumption_resolution,[],[f790,f106])).
% 1.93/0.62  fof(f106,plain,(
% 1.93/0.62    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 1.93/0.62    inference(equality_resolution,[],[f79])).
% 1.93/0.62  fof(f79,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 1.93/0.62    inference(cnf_transformation,[],[f49])).
% 1.93/0.62  fof(f49,plain,(
% 1.93/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.93/0.62    inference(flattening,[],[f48])).
% 1.93/0.62  fof(f48,plain,(
% 1.93/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.93/0.62    inference(nnf_transformation,[],[f5])).
% 1.93/0.62  fof(f5,axiom,(
% 1.93/0.62    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.93/0.62  fof(f790,plain,(
% 1.93/0.62    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.93/0.62    inference(backward_demodulation,[],[f492,f789])).
% 1.93/0.62  fof(f789,plain,(
% 1.93/0.62    ( ! [X4] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)) )),
% 1.93/0.62    inference(subsumption_resolution,[],[f788,f124])).
% 1.93/0.62  fof(f124,plain,(
% 1.93/0.62    v1_relat_1(k1_xboole_0)),
% 1.93/0.62    inference(superposition,[],[f64,f107])).
% 1.93/0.62  fof(f107,plain,(
% 1.93/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.93/0.62    inference(equality_resolution,[],[f85])).
% 1.93/0.62  fof(f85,plain,(
% 1.93/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.93/0.62    inference(cnf_transformation,[],[f52])).
% 1.93/0.62  fof(f52,plain,(
% 1.93/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.93/0.62    inference(flattening,[],[f51])).
% 1.93/0.62  fof(f51,plain,(
% 1.93/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.93/0.62    inference(nnf_transformation,[],[f6])).
% 1.93/0.62  fof(f6,axiom,(
% 1.93/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.93/0.62  fof(f64,plain,(
% 1.93/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.93/0.62    inference(cnf_transformation,[],[f11])).
% 1.93/0.62  fof(f11,axiom,(
% 1.93/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.93/0.62  fof(f788,plain,(
% 1.93/0.62    ( ! [X4] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X4) | ~v1_relat_1(k1_xboole_0)) )),
% 1.93/0.62    inference(subsumption_resolution,[],[f784,f539])).
% 1.93/0.62  fof(f539,plain,(
% 1.93/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.93/0.62    inference(subsumption_resolution,[],[f501,f179])).
% 1.93/0.62  fof(f179,plain,(
% 1.93/0.62    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.93/0.62    inference(superposition,[],[f171,f107])).
% 1.93/0.62  fof(f171,plain,(
% 1.93/0.62    ( ! [X0,X1] : (v4_relat_1(k2_zfmisc_1(X0,X1),X0)) )),
% 1.93/0.62    inference(resolution,[],[f150,f103])).
% 1.93/0.62  fof(f103,plain,(
% 1.93/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.93/0.62    inference(equality_resolution,[],[f76])).
% 1.93/0.62  fof(f76,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.93/0.62    inference(cnf_transformation,[],[f47])).
% 1.93/0.62  fof(f47,plain,(
% 1.93/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/0.62    inference(flattening,[],[f46])).
% 1.93/0.62  fof(f46,plain,(
% 1.93/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/0.62    inference(nnf_transformation,[],[f1])).
% 1.93/0.62  fof(f1,axiom,(
% 1.93/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.93/0.62  fof(f150,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 1.93/0.62    inference(resolution,[],[f88,f82])).
% 1.93/0.62  fof(f82,plain,(
% 1.93/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f50])).
% 1.93/0.62  fof(f50,plain,(
% 1.93/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.93/0.62    inference(nnf_transformation,[],[f7])).
% 1.93/0.62  fof(f7,axiom,(
% 1.93/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.93/0.62  fof(f88,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f36])).
% 1.93/0.62  fof(f36,plain,(
% 1.93/0.62    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.62    inference(ennf_transformation,[],[f16])).
% 1.93/0.62  fof(f16,axiom,(
% 1.93/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.93/0.62  fof(f501,plain,(
% 1.93/0.62    ( ! [X0] : (~v4_relat_1(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.93/0.62    inference(backward_demodulation,[],[f372,f482])).
% 1.93/0.62  fof(f482,plain,(
% 1.93/0.62    k1_xboole_0 = sK3),
% 1.93/0.62    inference(subsumption_resolution,[],[f481,f439])).
% 1.93/0.62  fof(f439,plain,(
% 1.93/0.62    r1_tarski(sK3,k1_xboole_0)),
% 1.93/0.62    inference(resolution,[],[f393,f103])).
% 1.93/0.62  fof(f393,plain,(
% 1.93/0.62    ( ! [X10] : (~r1_tarski(k2_relat_1(sK3),X10) | r1_tarski(sK3,k1_xboole_0)) )),
% 1.93/0.62    inference(forward_demodulation,[],[f392,f108])).
% 1.93/0.62  fof(f108,plain,(
% 1.93/0.62    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.93/0.62    inference(equality_resolution,[],[f84])).
% 1.93/0.62  fof(f84,plain,(
% 1.93/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.93/0.62    inference(cnf_transformation,[],[f52])).
% 1.93/0.62  fof(f392,plain,(
% 1.93/0.62    ( ! [X10] : (r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X10)) | ~r1_tarski(k2_relat_1(sK3),X10)) )),
% 1.93/0.62    inference(subsumption_resolution,[],[f391,f130])).
% 1.93/0.62  fof(f130,plain,(
% 1.93/0.62    v1_relat_1(sK3)),
% 1.93/0.62    inference(subsumption_resolution,[],[f128,f64])).
% 1.93/0.62  fof(f128,plain,(
% 1.93/0.62    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1))),
% 1.93/0.62    inference(resolution,[],[f62,f58])).
% 1.93/0.62  fof(f58,plain,(
% 1.93/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.93/0.62    inference(cnf_transformation,[],[f43])).
% 1.93/0.62  fof(f43,plain,(
% 1.93/0.62    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.93/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f42])).
% 1.93/0.62  fof(f42,plain,(
% 1.93/0.62    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.93/0.62    introduced(choice_axiom,[])).
% 1.93/0.62  fof(f24,plain,(
% 1.93/0.62    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.93/0.62    inference(flattening,[],[f23])).
% 1.93/0.62  fof(f23,plain,(
% 1.93/0.62    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.93/0.62    inference(ennf_transformation,[],[f22])).
% 1.93/0.62  fof(f22,negated_conjecture,(
% 1.93/0.62    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.93/0.62    inference(negated_conjecture,[],[f21])).
% 1.93/0.62  fof(f21,conjecture,(
% 1.93/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.93/0.62  fof(f62,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f25])).
% 1.93/0.62  fof(f25,plain,(
% 1.93/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.93/0.62    inference(ennf_transformation,[],[f8])).
% 1.93/0.62  fof(f8,axiom,(
% 1.93/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.93/0.62  fof(f391,plain,(
% 1.93/0.62    ( ! [X10] : (r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X10)) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X10)) )),
% 1.93/0.62    inference(subsumption_resolution,[],[f369,f56])).
% 1.93/0.62  fof(f56,plain,(
% 1.93/0.62    v1_funct_1(sK3)),
% 1.93/0.62    inference(cnf_transformation,[],[f43])).
% 1.93/0.62  fof(f369,plain,(
% 1.93/0.62    ( ! [X10] : (r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X10)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),X10)) )),
% 1.93/0.62    inference(superposition,[],[f185,f314])).
% 1.93/0.62  fof(f314,plain,(
% 1.93/0.62    k1_xboole_0 = k1_relat_1(sK3)),
% 1.93/0.62    inference(subsumption_resolution,[],[f313,f149])).
% 1.93/0.62  fof(f149,plain,(
% 1.93/0.62    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.93/0.62    inference(resolution,[],[f88,f58])).
% 1.93/0.62  fof(f313,plain,(
% 1.93/0.62    k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(sK0))),
% 1.93/0.62    inference(equality_resolution,[],[f310])).
% 1.93/0.62  fof(f310,plain,(
% 1.93/0.62    ( ! [X35] : (k1_tarski(sK0) != k1_tarski(X35) | k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(X35))) )),
% 1.93/0.62    inference(subsumption_resolution,[],[f286,f130])).
% 1.93/0.62  fof(f286,plain,(
% 1.93/0.62    ( ! [X35] : (k1_tarski(sK0) != k1_tarski(X35) | k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(X35)) | ~v1_relat_1(sK3)) )),
% 1.93/0.62    inference(superposition,[],[f199,f162])).
% 1.93/0.62  fof(f162,plain,(
% 1.93/0.62    ( ! [X2,X3] : (k1_relat_1(X2) = k1_tarski(X3) | k1_xboole_0 = k1_relat_1(X2) | ~v4_relat_1(X2,k1_tarski(X3)) | ~v1_relat_1(X2)) )),
% 1.93/0.62    inference(resolution,[],[f78,f69])).
% 1.93/0.62  fof(f69,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f45])).
% 1.93/0.62  fof(f45,plain,(
% 1.93/0.62    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.93/0.62    inference(nnf_transformation,[],[f30])).
% 1.93/0.62  fof(f30,plain,(
% 1.93/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.93/0.62    inference(ennf_transformation,[],[f9])).
% 1.93/0.62  fof(f9,axiom,(
% 1.93/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.93/0.62  fof(f78,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.93/0.62    inference(cnf_transformation,[],[f49])).
% 1.93/0.62  fof(f199,plain,(
% 1.93/0.62    k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.93/0.62    inference(subsumption_resolution,[],[f198,f130])).
% 1.93/0.62  fof(f198,plain,(
% 1.93/0.62    k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.93/0.62    inference(resolution,[],[f195,f66])).
% 1.93/0.62  fof(f66,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f28])).
% 1.93/0.62  fof(f28,plain,(
% 1.93/0.62    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.93/0.62    inference(ennf_transformation,[],[f12])).
% 1.93/0.62  fof(f12,axiom,(
% 1.93/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.93/0.62  fof(f195,plain,(
% 1.93/0.62    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.93/0.62    inference(subsumption_resolution,[],[f194,f130])).
% 1.93/0.62  fof(f194,plain,(
% 1.93/0.62    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.93/0.62    inference(subsumption_resolution,[],[f189,f56])).
% 1.93/0.62  fof(f189,plain,(
% 1.93/0.62    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.93/0.62    inference(superposition,[],[f188,f74])).
% 1.93/0.62  fof(f74,plain,(
% 1.93/0.62    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f34])).
% 1.93/0.62  fof(f34,plain,(
% 1.93/0.62    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.93/0.62    inference(flattening,[],[f33])).
% 1.93/0.62  fof(f33,plain,(
% 1.93/0.62    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.93/0.62    inference(ennf_transformation,[],[f14])).
% 1.93/0.62  fof(f14,axiom,(
% 1.93/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.93/0.62  fof(f188,plain,(
% 1.93/0.62    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.93/0.62    inference(subsumption_resolution,[],[f187,f58])).
% 1.93/0.62  fof(f187,plain,(
% 1.93/0.62    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.93/0.62    inference(superposition,[],[f60,f102])).
% 1.93/0.62  fof(f102,plain,(
% 1.93/0.62    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.93/0.62    inference(cnf_transformation,[],[f41])).
% 1.93/0.62  fof(f41,plain,(
% 1.93/0.62    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.62    inference(ennf_transformation,[],[f17])).
% 1.93/0.62  fof(f17,axiom,(
% 1.93/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.93/0.62  fof(f60,plain,(
% 1.93/0.62    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.93/0.62    inference(cnf_transformation,[],[f43])).
% 1.93/0.62  fof(f185,plain,(
% 1.93/0.62    ( ! [X8,X9] : (r1_tarski(X8,k2_zfmisc_1(k1_relat_1(X8),X9)) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~r1_tarski(k2_relat_1(X8),X9)) )),
% 1.93/0.62    inference(resolution,[],[f73,f81])).
% 1.93/0.62  fof(f81,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f50])).
% 1.93/0.62  fof(f73,plain,(
% 1.93/0.62    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f32])).
% 1.93/0.62  fof(f32,plain,(
% 1.93/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.93/0.62    inference(flattening,[],[f31])).
% 1.93/0.62  fof(f31,plain,(
% 1.93/0.62    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.93/0.62    inference(ennf_transformation,[],[f19])).
% 1.93/0.62  fof(f19,axiom,(
% 1.93/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.93/0.62  fof(f481,plain,(
% 1.93/0.62    k1_xboole_0 = sK3 | ~r1_tarski(sK3,k1_xboole_0)),
% 1.93/0.62    inference(resolution,[],[f452,f407])).
% 1.93/0.62  fof(f407,plain,(
% 1.93/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~r1_tarski(sK3,k1_xboole_0)) )),
% 1.93/0.62    inference(resolution,[],[f372,f159])).
% 1.93/0.62  fof(f159,plain,(
% 1.93/0.62    ( ! [X0,X1] : (v4_relat_1(X0,X1) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.93/0.62    inference(resolution,[],[f151,f82])).
% 1.93/0.62  fof(f151,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 1.93/0.62    inference(superposition,[],[f88,f107])).
% 1.93/0.62  fof(f452,plain,(
% 1.93/0.62    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3),
% 1.93/0.62    inference(resolution,[],[f439,f77])).
% 1.93/0.62  fof(f77,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f47])).
% 1.93/0.62  fof(f372,plain,(
% 1.93/0.62    ( ! [X0] : (~v4_relat_1(sK3,X0) | r1_tarski(k1_xboole_0,X0)) )),
% 1.93/0.62    inference(subsumption_resolution,[],[f358,f130])).
% 1.93/0.62  fof(f358,plain,(
% 1.93/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 1.93/0.62    inference(superposition,[],[f69,f314])).
% 1.93/0.62  fof(f784,plain,(
% 1.93/0.62    ( ! [X4] : (~r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X4)) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X4) | ~v1_relat_1(k1_xboole_0)) )),
% 1.93/0.62    inference(superposition,[],[f147,f759])).
% 1.93/0.62  fof(f759,plain,(
% 1.93/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.93/0.62    inference(subsumption_resolution,[],[f756,f124])).
% 1.93/0.62  fof(f756,plain,(
% 1.93/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.93/0.62    inference(resolution,[],[f532,f66])).
% 1.93/0.62  fof(f532,plain,(
% 1.93/0.62    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.93/0.62    inference(backward_demodulation,[],[f476,f482])).
% 1.93/0.62  fof(f476,plain,(
% 1.93/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0))),
% 1.93/0.62    inference(subsumption_resolution,[],[f471,f124])).
% 1.93/0.62  fof(f471,plain,(
% 1.93/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.93/0.62    inference(resolution,[],[f331,f223])).
% 1.93/0.62  fof(f223,plain,(
% 1.93/0.62    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 1.93/0.62    inference(superposition,[],[f215,f108])).
% 1.93/0.62  fof(f215,plain,(
% 1.93/0.62    ( ! [X0,X1] : (v5_relat_1(k2_zfmisc_1(X0,X1),X1)) )),
% 1.93/0.62    inference(resolution,[],[f154,f103])).
% 1.93/0.62  fof(f154,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | v5_relat_1(X0,X1)) )),
% 1.93/0.62    inference(resolution,[],[f89,f82])).
% 1.93/0.62  fof(f89,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f36])).
% 1.93/0.62  fof(f331,plain,(
% 1.93/0.62    ( ! [X7] : (~v5_relat_1(X7,k1_tarski(k1_funct_1(sK3,sK0))) | k1_xboole_0 = k2_relat_1(X7) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(X7)) | ~v1_relat_1(X7)) )),
% 1.93/0.62    inference(superposition,[],[f188,f163])).
% 1.93/0.62  fof(f163,plain,(
% 1.93/0.62    ( ! [X4,X5] : (k2_relat_1(X4) = k1_tarski(X5) | k1_xboole_0 = k2_relat_1(X4) | ~v5_relat_1(X4,k1_tarski(X5)) | ~v1_relat_1(X4)) )),
% 1.93/0.62    inference(resolution,[],[f78,f67])).
% 1.93/0.62  fof(f67,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f44])).
% 1.93/0.62  fof(f44,plain,(
% 1.93/0.62    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.93/0.62    inference(nnf_transformation,[],[f29])).
% 1.93/0.62  fof(f29,plain,(
% 1.93/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.93/0.62    inference(ennf_transformation,[],[f10])).
% 1.93/0.62  fof(f10,axiom,(
% 1.93/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.93/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.93/0.62  fof(f147,plain,(
% 1.93/0.62    ( ! [X6,X7] : (~r1_tarski(k2_relat_1(X6),k9_relat_1(X6,X7)) | k2_relat_1(X6) = k9_relat_1(X6,X7) | ~v1_relat_1(X6)) )),
% 1.93/0.62    inference(resolution,[],[f77,f66])).
% 1.93/0.62  fof(f492,plain,(
% 1.93/0.62    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.93/0.62    inference(backward_demodulation,[],[f188,f482])).
% 1.93/0.62  % SZS output end Proof for theBenchmark
% 1.93/0.62  % (6775)------------------------------
% 1.93/0.62  % (6775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.62  % (6775)Termination reason: Refutation
% 1.93/0.62  
% 1.93/0.62  % (6775)Memory used [KB]: 2046
% 1.93/0.62  % (6775)Time elapsed: 0.185 s
% 1.93/0.62  % (6775)------------------------------
% 1.93/0.62  % (6775)------------------------------
% 1.93/0.62  % (6765)Success in time 0.252 s
%------------------------------------------------------------------------------

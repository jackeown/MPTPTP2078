%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:26 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 217 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :   26
%              Number of atoms          :  275 ( 684 expanded)
%              Number of equality atoms :   82 ( 173 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f580,plain,(
    $false ),
    inference(subsumption_resolution,[],[f579,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f579,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f559,f137])).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f136,f63])).

fof(f63,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f136,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f135,f103])).

fof(f103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f64,f61])).

fof(f61,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f64,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f135,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f73,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f106,f103])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f72,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f559,plain,(
    ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f194,f548])).

% (2275)Termination reason: Refutation not found, incomplete strategy

% (2275)Memory used [KB]: 10746
% (2275)Time elapsed: 0.160 s
% (2275)------------------------------
% (2275)------------------------------
fof(f548,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f530,f70])).

fof(f530,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f522,f65])).

fof(f522,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f355,f513])).

fof(f513,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f512,f131])).

fof(f131,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f47])).

fof(f47,plain,
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

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f512,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f452])).

fof(f452,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v4_relat_1(sK3,k1_tarski(X0)) ) ),
    inference(subsumption_resolution,[],[f449,f113])).

fof(f113,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f89,f58])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f449,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v4_relat_1(sK3,k1_tarski(X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f435,f147])).

fof(f147,plain,(
    ! [X4,X5] :
      ( k1_relat_1(X4) = k1_tarski(X5)
      | k1_xboole_0 = k1_relat_1(X4)
      | ~ v4_relat_1(X4,k1_tarski(X5))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f82,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f435,plain,(
    k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f434,f113])).

fof(f434,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f410,f72])).

fof(f410,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f409,f113])).

fof(f409,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3)
    | k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(resolution,[],[f177,f199])).

fof(f199,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f198,f113])).

fof(f198,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f195,f57])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f195,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_tarski(sK0) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f194,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f177,plain,(
    ! [X2,X3,X1] :
      ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X3))
      | ~ r1_tarski(k7_relat_1(X1,X2),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f172,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f172,plain,(
    ! [X2,X3,X1] :
      ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X3))
      | ~ r1_tarski(k7_relat_1(X1,X2),X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X1,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f68,f73])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f355,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(resolution,[],[f309,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f309,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    inference(resolution,[],[f207,f58])).

fof(f207,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X3)))
      | ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
      | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f93,f102])).

fof(f102,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f194,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(subsumption_resolution,[],[f193,f58])).

fof(f193,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(superposition,[],[f60,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (2277)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (2287)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (2279)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (2292)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (2269)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (2271)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (2279)Refutation not found, incomplete strategy% (2279)------------------------------
% 0.21/0.52  % (2279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2279)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2279)Memory used [KB]: 1791
% 0.21/0.52  % (2279)Time elapsed: 0.063 s
% 0.21/0.52  % (2279)------------------------------
% 0.21/0.52  % (2279)------------------------------
% 0.21/0.52  % (2284)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (2265)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (2266)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (2270)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (2291)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (2292)Refutation not found, incomplete strategy% (2292)------------------------------
% 0.21/0.53  % (2292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2289)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (2268)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (2274)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (2292)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  % (2267)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  
% 0.21/0.54  % (2292)Memory used [KB]: 6268
% 0.21/0.54  % (2292)Time elapsed: 0.115 s
% 0.21/0.54  % (2292)------------------------------
% 0.21/0.54  % (2292)------------------------------
% 0.21/0.54  % (2289)Refutation not found, incomplete strategy% (2289)------------------------------
% 0.21/0.54  % (2289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2283)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (2294)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (2281)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (2289)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2289)Memory used [KB]: 10618
% 0.21/0.54  % (2289)Time elapsed: 0.129 s
% 0.21/0.54  % (2289)------------------------------
% 0.21/0.54  % (2289)------------------------------
% 0.21/0.55  % (2283)Refutation not found, incomplete strategy% (2283)------------------------------
% 0.21/0.55  % (2283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2276)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (2281)Refutation not found, incomplete strategy% (2281)------------------------------
% 0.21/0.55  % (2281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (2282)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.55  % (2273)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.55  % (2286)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.55  % (2272)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.55  % (2285)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.55  % (2275)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.55  % (2290)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.55  % (2278)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.55  % (2294)Refutation not found, incomplete strategy% (2294)------------------------------
% 1.39/0.55  % (2294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (2281)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (2281)Memory used [KB]: 10746
% 1.39/0.55  % (2281)Time elapsed: 0.138 s
% 1.39/0.55  % (2281)------------------------------
% 1.39/0.55  % (2281)------------------------------
% 1.39/0.56  % (2288)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.56  % (2293)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.57  % (2294)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (2294)Memory used [KB]: 1663
% 1.39/0.57  % (2294)Time elapsed: 0.138 s
% 1.39/0.57  % (2294)------------------------------
% 1.39/0.57  % (2294)------------------------------
% 1.39/0.57  % (2282)Refutation not found, incomplete strategy% (2282)------------------------------
% 1.39/0.57  % (2282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (2283)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (2283)Memory used [KB]: 1791
% 1.39/0.57  % (2283)Time elapsed: 0.131 s
% 1.39/0.57  % (2283)------------------------------
% 1.39/0.57  % (2283)------------------------------
% 1.53/0.57  % (2275)Refutation not found, incomplete strategy% (2275)------------------------------
% 1.53/0.57  % (2275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (2282)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (2282)Memory used [KB]: 1791
% 1.53/0.57  % (2282)Time elapsed: 0.148 s
% 1.53/0.57  % (2282)------------------------------
% 1.53/0.57  % (2282)------------------------------
% 1.53/0.57  % (2274)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f580,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(subsumption_resolution,[],[f579,f65])).
% 1.53/0.57  fof(f65,plain,(
% 1.53/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.53/0.57  fof(f579,plain,(
% 1.53/0.57    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.53/0.57    inference(forward_demodulation,[],[f559,f137])).
% 1.53/0.57  fof(f137,plain,(
% 1.53/0.57    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(forward_demodulation,[],[f136,f63])).
% 1.53/0.57  fof(f63,plain,(
% 1.53/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.53/0.57    inference(cnf_transformation,[],[f19])).
% 1.53/0.57  fof(f19,axiom,(
% 1.53/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.53/0.57  fof(f136,plain,(
% 1.53/0.57    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f135,f103])).
% 1.53/0.57  fof(f103,plain,(
% 1.53/0.57    v1_relat_1(k1_xboole_0)),
% 1.53/0.57    inference(superposition,[],[f64,f61])).
% 1.53/0.57  fof(f61,plain,(
% 1.53/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.53/0.57    inference(cnf_transformation,[],[f20])).
% 1.53/0.57  fof(f20,axiom,(
% 1.53/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.53/0.57  fof(f64,plain,(
% 1.53/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f16])).
% 1.53/0.57  fof(f16,axiom,(
% 1.53/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.53/0.57  fof(f135,plain,(
% 1.53/0.57    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.53/0.57    inference(superposition,[],[f73,f107])).
% 1.53/0.57  fof(f107,plain,(
% 1.53/0.57    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f106,f103])).
% 1.53/0.57  fof(f106,plain,(
% 1.53/0.57    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(resolution,[],[f72,f70])).
% 1.53/0.57  fof(f70,plain,(
% 1.53/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f36])).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.53/0.57    inference(ennf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.53/0.57  fof(f72,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f37])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f21])).
% 1.53/0.57  fof(f21,axiom,(
% 1.53/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.53/0.57  fof(f73,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f17])).
% 1.53/0.57  fof(f17,axiom,(
% 1.53/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.53/0.57  fof(f559,plain,(
% 1.53/0.57    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.53/0.57    inference(backward_demodulation,[],[f194,f548])).
% 1.53/0.57  % (2275)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (2275)Memory used [KB]: 10746
% 1.53/0.57  % (2275)Time elapsed: 0.160 s
% 1.53/0.57  % (2275)------------------------------
% 1.53/0.57  % (2275)------------------------------
% 1.53/0.57  fof(f548,plain,(
% 1.53/0.57    k1_xboole_0 = sK3),
% 1.53/0.57    inference(resolution,[],[f530,f70])).
% 1.53/0.57  fof(f530,plain,(
% 1.53/0.57    r1_tarski(sK3,k1_xboole_0)),
% 1.53/0.57    inference(subsumption_resolution,[],[f522,f65])).
% 1.53/0.57  fof(f522,plain,(
% 1.53/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(sK3,k1_xboole_0)),
% 1.53/0.57    inference(backward_demodulation,[],[f355,f513])).
% 1.53/0.57  fof(f513,plain,(
% 1.53/0.57    k1_xboole_0 = k1_relat_1(sK3)),
% 1.53/0.57    inference(subsumption_resolution,[],[f512,f131])).
% 1.53/0.57  fof(f131,plain,(
% 1.53/0.57    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.53/0.57    inference(resolution,[],[f90,f58])).
% 1.53/0.57  fof(f58,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.53/0.57    inference(cnf_transformation,[],[f48])).
% 1.53/0.57  fof(f48,plain,(
% 1.53/0.57    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f47])).
% 1.53/0.57  fof(f47,plain,(
% 1.53/0.57    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.53/0.57    inference(flattening,[],[f31])).
% 1.53/0.57  fof(f31,plain,(
% 1.53/0.57    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.53/0.57    inference(ennf_transformation,[],[f29])).
% 1.53/0.57  fof(f29,plain,(
% 1.53/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.53/0.57    inference(pure_predicate_removal,[],[f28])).
% 1.53/0.57  fof(f28,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.53/0.57    inference(negated_conjecture,[],[f27])).
% 1.53/0.57  fof(f27,conjecture,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.53/0.57  fof(f90,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f43])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(ennf_transformation,[],[f30])).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.53/0.57    inference(pure_predicate_removal,[],[f24])).
% 1.53/0.57  fof(f24,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.53/0.57  fof(f512,plain,(
% 1.53/0.57    k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(sK0))),
% 1.53/0.57    inference(equality_resolution,[],[f452])).
% 1.53/0.57  fof(f452,plain,(
% 1.53/0.57    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(X0))) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f449,f113])).
% 1.53/0.57  fof(f113,plain,(
% 1.53/0.57    v1_relat_1(sK3)),
% 1.53/0.57    inference(resolution,[],[f89,f58])).
% 1.53/0.57  fof(f89,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f42])).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(ennf_transformation,[],[f23])).
% 1.53/0.57  fof(f23,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.53/0.57  fof(f449,plain,(
% 1.53/0.57    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k1_xboole_0 = k1_relat_1(sK3) | ~v4_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3)) )),
% 1.53/0.57    inference(superposition,[],[f435,f147])).
% 1.53/0.57  fof(f147,plain,(
% 1.53/0.57    ( ! [X4,X5] : (k1_relat_1(X4) = k1_tarski(X5) | k1_xboole_0 = k1_relat_1(X4) | ~v4_relat_1(X4,k1_tarski(X5)) | ~v1_relat_1(X4)) )),
% 1.53/0.57    inference(resolution,[],[f82,f74])).
% 1.53/0.57  fof(f74,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f49])).
% 1.53/0.57  fof(f49,plain,(
% 1.53/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(nnf_transformation,[],[f39])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,axiom,(
% 1.53/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.53/0.57  fof(f82,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f54])).
% 1.53/0.57  fof(f54,plain,(
% 1.53/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.53/0.57    inference(flattening,[],[f53])).
% 1.53/0.57  fof(f53,plain,(
% 1.53/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.53/0.57    inference(nnf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,axiom,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.53/0.57  fof(f435,plain,(
% 1.53/0.57    k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.53/0.57    inference(subsumption_resolution,[],[f434,f113])).
% 1.53/0.57  fof(f434,plain,(
% 1.53/0.57    k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.53/0.57    inference(resolution,[],[f410,f72])).
% 1.53/0.57  fof(f410,plain,(
% 1.53/0.57    ~r1_tarski(k7_relat_1(sK3,sK2),sK3) | k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.53/0.57    inference(subsumption_resolution,[],[f409,f113])).
% 1.53/0.57  fof(f409,plain,(
% 1.53/0.57    ~r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~v1_relat_1(sK3) | k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f402])).
% 1.53/0.57  fof(f402,plain,(
% 1.53/0.57    ~r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3) | k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.53/0.57    inference(resolution,[],[f177,f199])).
% 1.53/0.57  fof(f199,plain,(
% 1.53/0.57    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3)),
% 1.53/0.57    inference(subsumption_resolution,[],[f198,f113])).
% 1.53/0.57  fof(f198,plain,(
% 1.53/0.57    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.53/0.57    inference(subsumption_resolution,[],[f195,f57])).
% 1.53/0.57  fof(f57,plain,(
% 1.53/0.57    v1_funct_1(sK3)),
% 1.53/0.57    inference(cnf_transformation,[],[f48])).
% 1.53/0.57  fof(f195,plain,(
% 1.53/0.57    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_tarski(sK0) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.53/0.57    inference(superposition,[],[f194,f76])).
% 1.53/0.57  fof(f76,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f41])).
% 1.53/0.57  fof(f41,plain,(
% 1.53/0.57    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(flattening,[],[f40])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f22])).
% 1.53/0.57  fof(f22,axiom,(
% 1.53/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.53/0.57  fof(f177,plain,(
% 1.53/0.57    ( ! [X2,X3,X1] : (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X3)) | ~r1_tarski(k7_relat_1(X1,X2),X3) | ~v1_relat_1(X3) | ~v1_relat_1(X1)) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f172,f112])).
% 1.53/0.57  fof(f112,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.53/0.57    inference(resolution,[],[f69,f81])).
% 1.53/0.57  fof(f81,plain,(
% 1.53/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f52])).
% 1.53/0.57  fof(f52,plain,(
% 1.53/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.53/0.57    inference(nnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,axiom,(
% 1.53/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.53/0.57  fof(f69,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f35])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f14])).
% 1.53/0.57  fof(f14,axiom,(
% 1.53/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.53/0.57  fof(f172,plain,(
% 1.53/0.57    ( ! [X2,X3,X1] : (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X3)) | ~r1_tarski(k7_relat_1(X1,X2),X3) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X1,X2)) | ~v1_relat_1(X1)) )),
% 1.53/0.57    inference(superposition,[],[f68,f73])).
% 1.53/0.57  fof(f68,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f34])).
% 1.53/0.57  fof(f34,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(flattening,[],[f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f18])).
% 1.53/0.57  fof(f18,axiom,(
% 1.53/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.53/0.57  fof(f355,plain,(
% 1.53/0.57    ~r1_tarski(k1_relat_1(sK3),k1_xboole_0) | r1_tarski(sK3,k1_xboole_0)),
% 1.53/0.57    inference(resolution,[],[f309,f80])).
% 1.53/0.57  fof(f80,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f52])).
% 1.53/0.57  fof(f309,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 1.53/0.57    inference(resolution,[],[f207,f58])).
% 1.53/0.57  fof(f207,plain,(
% 1.53/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X3))) | ~r1_tarski(k1_relat_1(X4),k1_xboole_0) | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))) )),
% 1.53/0.57    inference(superposition,[],[f93,f102])).
% 1.53/0.57  fof(f102,plain,(
% 1.53/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.53/0.57    inference(equality_resolution,[],[f86])).
% 1.53/0.57  fof(f86,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f56])).
% 1.53/0.57  fof(f56,plain,(
% 1.53/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.53/0.57    inference(flattening,[],[f55])).
% 1.53/0.57  fof(f55,plain,(
% 1.53/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.53/0.57    inference(nnf_transformation,[],[f12])).
% 1.53/0.57  fof(f12,axiom,(
% 1.53/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.53/0.57  fof(f93,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f46])).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.53/0.57    inference(flattening,[],[f45])).
% 1.53/0.57  fof(f45,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.53/0.57    inference(ennf_transformation,[],[f26])).
% 1.53/0.57  fof(f26,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 1.53/0.57  fof(f194,plain,(
% 1.53/0.57    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.53/0.57    inference(subsumption_resolution,[],[f193,f58])).
% 1.53/0.57  fof(f193,plain,(
% 1.53/0.57    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.53/0.57    inference(superposition,[],[f60,f92])).
% 1.53/0.57  fof(f92,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f44])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(ennf_transformation,[],[f25])).
% 1.53/0.57  fof(f25,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.53/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.53/0.57  fof(f60,plain,(
% 1.53/0.57    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.53/0.57    inference(cnf_transformation,[],[f48])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (2274)------------------------------
% 1.53/0.57  % (2274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (2274)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (2274)Memory used [KB]: 1918
% 1.53/0.57  % (2274)Time elapsed: 0.149 s
% 1.53/0.57  % (2274)------------------------------
% 1.53/0.57  % (2274)------------------------------
% 1.53/0.57  % (2264)Success in time 0.204 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 143 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   22
%              Number of atoms          :  185 ( 447 expanded)
%              Number of equality atoms :   36 (  99 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(subsumption_resolution,[],[f327,f83])).

fof(f83,plain,(
    r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_relat_1(X0),sK2)
      | r1_tarski(X0,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f32,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f327,plain,(
    ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f276])).

fof(f276,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f61,f273])).

fof(f273,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f246,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f246,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | sK1 = k2_relat_1(sK2) ) ),
    inference(resolution,[],[f232,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f232,plain,
    ( ~ v4_relat_1(k6_relat_1(sK1),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f225,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f225,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v4_relat_1(k6_relat_1(sK1),sK1)
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f206,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v4_relat_1(X0,k2_relat_1(sK2))
      | ~ v4_relat_1(X0,sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f76,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f76,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f60,f33])).

fof(f60,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_relat_1(X1),sK2)
      | r1_tarski(X1,k2_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f55,f58])).

fof(f58,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f55,plain,(
    ! [X1] :
      ( r1_tarski(X1,k2_relset_1(sK0,sK1,sK2))
      | ~ r1_tarski(k6_relat_1(X1),sK2) ) ),
    inference(resolution,[],[f32,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f206,plain,
    ( ~ v4_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f205,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f205,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v4_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f202,f35])).

fof(f202,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v4_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f190,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f190,plain,(
    k2_relat_1(sK2) = k1_relat_1(k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))) ),
    inference(resolution,[],[f158,f57])).

fof(f57,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f32,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f158,plain,(
    ! [X2] :
      ( ~ v5_relat_1(sK2,X2)
      | k2_relat_1(sK2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),k2_relat_1(sK2))) ) ),
    inference(forward_demodulation,[],[f155,f37])).

fof(f155,plain,(
    ! [X2] :
      ( k2_relat_1(sK2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),k2_relat_1(sK2)))
      | ~ v5_relat_1(sK2,k1_relat_1(k6_relat_1(X2))) ) ),
    inference(resolution,[],[f96,f35])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(sK2) = k1_relat_1(k7_relat_1(X1,k2_relat_1(sK2)))
      | ~ v5_relat_1(sK2,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f65,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f65,plain,(
    ! [X3] :
      ( r1_tarski(k2_relat_1(sK2),X3)
      | ~ v5_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f62,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f61,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f34,f58])).

fof(f34,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n018.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 20:32:12 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.48  % (9252)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.49  % (9252)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (9261)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.49  % (9261)Refutation not found, incomplete strategy% (9261)------------------------------
% 0.22/0.49  % (9261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9261)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9261)Memory used [KB]: 6140
% 0.22/0.49  % (9261)Time elapsed: 0.065 s
% 0.22/0.49  % (9261)------------------------------
% 0.22/0.49  % (9261)------------------------------
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f328,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f327,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    inference(resolution,[],[f54,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(k6_relat_1(X0),sK2) | r1_tarski(X0,k1_relset_1(sK0,sK1,sK2))) )),
% 0.22/0.50    inference(resolution,[],[f32,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f327,plain,(
% 0.22/0.50    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f276])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    sK1 != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f61,f273])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    sK1 = k2_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f246,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | sK1 = k2_relat_1(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f232,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    ~v4_relat_1(k6_relat_1(sK1),sK1) | sK1 = k2_relat_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f225,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    sK1 = k2_relat_1(sK2) | ~v4_relat_1(k6_relat_1(sK1),sK1) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.50    inference(resolution,[],[f206,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0] : (v4_relat_1(X0,k2_relat_1(sK2)) | ~v4_relat_1(X0,sK1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f76,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.50    inference(resolution,[],[f60,f33])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(k6_relat_1(X1),sK2) | r1_tarski(X1,k2_relat_1(sK2))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f55,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.50    inference(resolution,[],[f32,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,k2_relset_1(sK0,sK1,sK2)) | ~r1_tarski(k6_relat_1(X1),sK2)) )),
% 0.22/0.50    inference(resolution,[],[f32,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ~v4_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2)),
% 0.22/0.50    inference(forward_demodulation,[],[f205,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v4_relat_1(k6_relat_1(sK1),k2_relat_1(sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f202,f35])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v4_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.50    inference(superposition,[],[f190,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k1_relat_1(k7_relat_1(k6_relat_1(sK1),k2_relat_1(sK2)))),
% 0.22/0.50    inference(resolution,[],[f158,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v5_relat_1(sK2,sK1)),
% 0.22/0.50    inference(resolution,[],[f32,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ( ! [X2] : (~v5_relat_1(sK2,X2) | k2_relat_1(sK2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),k2_relat_1(sK2)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f155,f37])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ( ! [X2] : (k2_relat_1(sK2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),k2_relat_1(sK2))) | ~v5_relat_1(sK2,k1_relat_1(k6_relat_1(X2)))) )),
% 0.22/0.50    inference(resolution,[],[f96,f35])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(sK2) = k1_relat_1(k7_relat_1(X1,k2_relat_1(sK2))) | ~v5_relat_1(sK2,k1_relat_1(X1))) )),
% 0.22/0.50    inference(resolution,[],[f65,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X3] : (r1_tarski(k2_relat_1(sK2),X3) | ~v5_relat_1(sK2,X3)) )),
% 0.22/0.50    inference(resolution,[],[f62,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f59,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    inference(resolution,[],[f32,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    sK1 != k2_relat_1(sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f34,f58])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    sK1 != k2_relset_1(sK0,sK1,sK2) | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (9252)------------------------------
% 0.22/0.50  % (9252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9252)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (9252)Memory used [KB]: 1791
% 0.22/0.50  % (9252)Time elapsed: 0.066 s
% 0.22/0.50  % (9252)------------------------------
% 0.22/0.50  % (9252)------------------------------
% 0.22/0.50  % (9240)Success in time 0.12 s
%------------------------------------------------------------------------------

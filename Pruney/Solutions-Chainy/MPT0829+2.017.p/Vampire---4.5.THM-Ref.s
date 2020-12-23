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
% DateTime   : Thu Dec  3 12:56:43 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 500 expanded)
%              Number of leaves         :   15 ( 122 expanded)
%              Depth                    :   19
%              Number of atoms          :  168 (1150 expanded)
%              Number of equality atoms :   37 ( 217 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1399,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1398,f457])).

fof(f457,plain,(
    ~ r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f326,f455])).

fof(f455,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f326,plain,(
    ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f267,f325])).

fof(f325,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f166,f324])).

fof(f324,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f322,f30])).

fof(f30,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f322,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f314,f123])).

fof(f123,plain,(
    ! [X4] :
      ( ~ v5_relat_1(k6_relat_1(sK1),X4)
      | r1_tarski(sK1,X4) ) ),
    inference(forward_demodulation,[],[f122,f32])).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f122,plain,(
    ! [X4] :
      ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),X4)
      | ~ v5_relat_1(k6_relat_1(sK1),X4) ) ),
    inference(resolution,[],[f38,f75])).

fof(f75,plain,(
    v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f73,f30])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f72,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f70,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f70,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f55,f29])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f314,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(sK2))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f312,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f50,f43])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f312,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f64,f95])).

fof(f95,plain,(
    k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f88,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f88,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f33,f70])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f166,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f163,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f163,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f155,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | r1_tarski(X0,sK1) ) ),
    inference(superposition,[],[f64,f150])).

fof(f150,plain,(
    sK1 = k2_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f148,f126])).

fof(f126,plain,(
    ! [X1] :
      ( ~ v5_relat_1(sK2,X1)
      | k2_xboole_0(k2_relat_1(sK2),X1) = X1 ) ),
    inference(resolution,[],[f121,f39])).

fof(f121,plain,(
    ! [X3] :
      ( r1_tarski(k2_relat_1(sK2),X3)
      | ~ v5_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f38,f70])).

fof(f148,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f50,f29])).

fof(f267,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f28,f265])).

fof(f265,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f46,f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f28,plain,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f1398,plain,(
    r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f1390,f996])).

fof(f996,plain,(
    sK1 = k1_relset_1(k1_relat_1(sK2),sK1,k6_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f979,f31])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f979,plain,(
    k1_relat_1(k6_relat_1(sK1)) = k1_relset_1(k1_relat_1(sK2),sK1,k6_relat_1(sK1)) ),
    inference(resolution,[],[f456,f713])).

fof(f713,plain,(
    r1_tarski(k6_relat_1(sK1),k2_zfmisc_1(k1_relat_1(sK2),sK1)) ),
    inference(superposition,[],[f703,f328])).

fof(f328,plain,(
    k2_zfmisc_1(k1_relat_1(sK2),sK1) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK1)) ),
    inference(backward_demodulation,[],[f95,f325])).

fof(f703,plain,(
    ! [X0] : r1_tarski(k6_relat_1(sK1),k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f697,f36])).

fof(f697,plain,(
    ! [X0] : r1_tarski(k6_relat_1(sK1),k2_xboole_0(X0,sK2)) ),
    inference(resolution,[],[f692,f51])).

fof(f692,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,k6_relat_1(sK1))
      | r1_tarski(X5,k2_xboole_0(X4,sK2)) ) ),
    inference(superposition,[],[f64,f632])).

fof(f632,plain,(
    ! [X37] : k2_xboole_0(X37,sK2) = k2_xboole_0(k6_relat_1(sK1),k2_xboole_0(X37,sK2)) ),
    inference(resolution,[],[f63,f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X2,X1) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ) ),
    inference(resolution,[],[f45,f39])).

fof(f456,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(resolution,[],[f47,f43])).

fof(f1390,plain,(
    r1_tarski(k1_relset_1(k1_relat_1(sK2),sK1,k6_relat_1(sK1)),k1_relat_1(sK2)) ),
    inference(resolution,[],[f1099,f713])).

fof(f1099,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | r1_tarski(k1_relset_1(X0,X1,X2),X0) ) ),
    inference(resolution,[],[f519,f43])).

fof(f519,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relset_1(X1,X2,X0),X1) ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (27260)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (27262)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (27268)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (27259)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (27265)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (27270)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (27265)Refutation not found, incomplete strategy% (27265)------------------------------
% 0.21/0.50  % (27265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27265)Memory used [KB]: 10618
% 0.21/0.50  % (27265)Time elapsed: 0.095 s
% 0.21/0.50  % (27265)------------------------------
% 0.21/0.50  % (27265)------------------------------
% 0.21/0.51  % (27273)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (27274)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (27282)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (27278)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (27266)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (27284)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (27261)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (27263)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (27272)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (27269)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (27280)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (27276)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (27260)Refutation not found, incomplete strategy% (27260)------------------------------
% 0.21/0.52  % (27260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27260)Memory used [KB]: 10618
% 0.21/0.52  % (27260)Time elapsed: 0.115 s
% 0.21/0.52  % (27260)------------------------------
% 0.21/0.52  % (27260)------------------------------
% 0.21/0.52  % (27281)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (27264)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (27264)Refutation not found, incomplete strategy% (27264)------------------------------
% 0.21/0.53  % (27264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27264)Memory used [KB]: 6140
% 0.21/0.53  % (27264)Time elapsed: 0.125 s
% 0.21/0.53  % (27264)------------------------------
% 0.21/0.53  % (27264)------------------------------
% 0.21/0.53  % (27279)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (27271)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (27272)Refutation not found, incomplete strategy% (27272)------------------------------
% 0.21/0.53  % (27272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27272)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27272)Memory used [KB]: 6396
% 0.21/0.53  % (27272)Time elapsed: 0.131 s
% 0.21/0.53  % (27272)------------------------------
% 0.21/0.53  % (27272)------------------------------
% 0.21/0.54  % (27275)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (27267)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (27277)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (27283)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.85/0.59  % (27268)Refutation not found, incomplete strategy% (27268)------------------------------
% 1.85/0.59  % (27268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.59  % (27268)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.59  
% 1.85/0.59  % (27268)Memory used [KB]: 6140
% 1.85/0.59  % (27268)Time elapsed: 0.188 s
% 1.85/0.59  % (27268)------------------------------
% 1.85/0.59  % (27268)------------------------------
% 2.15/0.63  % (27278)Refutation found. Thanks to Tanya!
% 2.15/0.63  % SZS status Theorem for theBenchmark
% 2.15/0.63  % SZS output start Proof for theBenchmark
% 2.15/0.63  fof(f1399,plain,(
% 2.15/0.63    $false),
% 2.15/0.63    inference(subsumption_resolution,[],[f1398,f457])).
% 2.15/0.63  fof(f457,plain,(
% 2.15/0.63    ~r1_tarski(sK1,k1_relat_1(sK2))),
% 2.15/0.63    inference(backward_demodulation,[],[f326,f455])).
% 2.15/0.63  fof(f455,plain,(
% 2.15/0.63    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 2.15/0.63    inference(resolution,[],[f47,f29])).
% 2.15/0.63  fof(f29,plain,(
% 2.15/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.15/0.63    inference(cnf_transformation,[],[f18])).
% 2.15/0.63  fof(f18,plain,(
% 2.15/0.63    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.63    inference(flattening,[],[f17])).
% 2.15/0.63  fof(f17,plain,(
% 2.15/0.63    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.63    inference(ennf_transformation,[],[f16])).
% 2.15/0.63  fof(f16,negated_conjecture,(
% 2.15/0.63    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 2.15/0.63    inference(negated_conjecture,[],[f15])).
% 2.15/0.63  fof(f15,conjecture,(
% 2.15/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).
% 2.15/0.63  fof(f47,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f25])).
% 2.15/0.63  fof(f25,plain,(
% 2.15/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.63    inference(ennf_transformation,[],[f13])).
% 2.15/0.63  fof(f13,axiom,(
% 2.15/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.15/0.63  fof(f326,plain,(
% 2.15/0.63    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 2.15/0.63    inference(subsumption_resolution,[],[f267,f325])).
% 2.15/0.63  fof(f325,plain,(
% 2.15/0.63    sK1 = k2_relat_1(sK2)),
% 2.15/0.63    inference(subsumption_resolution,[],[f166,f324])).
% 2.15/0.63  fof(f324,plain,(
% 2.15/0.63    r1_tarski(sK1,k2_relat_1(sK2))),
% 2.15/0.63    inference(subsumption_resolution,[],[f322,f30])).
% 2.15/0.63  fof(f30,plain,(
% 2.15/0.63    r1_tarski(k6_relat_1(sK1),sK2)),
% 2.15/0.63    inference(cnf_transformation,[],[f18])).
% 2.15/0.63  fof(f322,plain,(
% 2.15/0.63    ~r1_tarski(k6_relat_1(sK1),sK2) | r1_tarski(sK1,k2_relat_1(sK2))),
% 2.15/0.63    inference(resolution,[],[f314,f123])).
% 2.15/0.63  fof(f123,plain,(
% 2.15/0.63    ( ! [X4] : (~v5_relat_1(k6_relat_1(sK1),X4) | r1_tarski(sK1,X4)) )),
% 2.15/0.63    inference(forward_demodulation,[],[f122,f32])).
% 2.15/0.63  fof(f32,plain,(
% 2.15/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.15/0.63    inference(cnf_transformation,[],[f10])).
% 2.15/0.63  fof(f10,axiom,(
% 2.15/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.15/0.63  fof(f122,plain,(
% 2.15/0.63    ( ! [X4] : (r1_tarski(k2_relat_1(k6_relat_1(sK1)),X4) | ~v5_relat_1(k6_relat_1(sK1),X4)) )),
% 2.15/0.63    inference(resolution,[],[f38,f75])).
% 2.15/0.63  fof(f75,plain,(
% 2.15/0.63    v1_relat_1(k6_relat_1(sK1))),
% 2.15/0.63    inference(resolution,[],[f73,f30])).
% 2.15/0.63  fof(f73,plain,(
% 2.15/0.63    ( ! [X0] : (~r1_tarski(X0,sK2) | v1_relat_1(X0)) )),
% 2.15/0.63    inference(resolution,[],[f72,f43])).
% 2.15/0.63  fof(f43,plain,(
% 2.15/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f5])).
% 2.15/0.63  fof(f5,axiom,(
% 2.15/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.15/0.63  fof(f72,plain,(
% 2.15/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_relat_1(X0)) )),
% 2.15/0.63    inference(resolution,[],[f70,f34])).
% 2.15/0.63  fof(f34,plain,(
% 2.15/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f20])).
% 2.15/0.63  fof(f20,plain,(
% 2.15/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.15/0.63    inference(ennf_transformation,[],[f6])).
% 2.15/0.63  fof(f6,axiom,(
% 2.15/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.15/0.63  fof(f70,plain,(
% 2.15/0.63    v1_relat_1(sK2)),
% 2.15/0.63    inference(resolution,[],[f55,f29])).
% 2.15/0.63  fof(f55,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 2.15/0.63    inference(resolution,[],[f34,f35])).
% 2.15/0.63  fof(f35,plain,(
% 2.15/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.15/0.63    inference(cnf_transformation,[],[f8])).
% 2.15/0.63  fof(f8,axiom,(
% 2.15/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.15/0.63  fof(f38,plain,(
% 2.15/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f21])).
% 2.15/0.63  fof(f21,plain,(
% 2.15/0.63    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.15/0.63    inference(ennf_transformation,[],[f7])).
% 2.15/0.63  fof(f7,axiom,(
% 2.15/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.15/0.63  fof(f314,plain,(
% 2.15/0.63    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(sK2)) | ~r1_tarski(X0,sK2)) )),
% 2.15/0.63    inference(resolution,[],[f312,f149])).
% 2.15/0.63  fof(f149,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | v5_relat_1(X0,X1)) )),
% 2.15/0.63    inference(resolution,[],[f50,f43])).
% 2.15/0.63  fof(f50,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f27])).
% 2.15/0.63  fof(f27,plain,(
% 2.15/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.63    inference(ennf_transformation,[],[f11])).
% 2.15/0.63  fof(f11,axiom,(
% 2.15/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.15/0.63  fof(f312,plain,(
% 2.15/0.63    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) | ~r1_tarski(X0,sK2)) )),
% 2.15/0.63    inference(superposition,[],[f64,f95])).
% 2.15/0.63  fof(f95,plain,(
% 2.15/0.63    k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 2.15/0.63    inference(resolution,[],[f88,f39])).
% 2.15/0.63  fof(f39,plain,(
% 2.15/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.15/0.63    inference(cnf_transformation,[],[f22])).
% 2.15/0.63  fof(f22,plain,(
% 2.15/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.15/0.63    inference(ennf_transformation,[],[f4])).
% 2.15/0.63  fof(f4,axiom,(
% 2.15/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.15/0.63  fof(f88,plain,(
% 2.15/0.63    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 2.15/0.63    inference(resolution,[],[f33,f70])).
% 2.15/0.63  fof(f33,plain,(
% 2.15/0.63    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.15/0.63    inference(cnf_transformation,[],[f19])).
% 2.15/0.63  fof(f19,plain,(
% 2.15/0.63    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.15/0.63    inference(ennf_transformation,[],[f9])).
% 2.15/0.63  fof(f9,axiom,(
% 2.15/0.63    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 2.15/0.63  fof(f64,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) )),
% 2.15/0.63    inference(superposition,[],[f45,f36])).
% 2.15/0.63  fof(f36,plain,(
% 2.15/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f1])).
% 2.15/0.63  fof(f1,axiom,(
% 2.15/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.15/0.63  fof(f45,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f23])).
% 2.15/0.63  fof(f23,plain,(
% 2.15/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.15/0.63    inference(ennf_transformation,[],[f3])).
% 2.15/0.63  fof(f3,axiom,(
% 2.15/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.15/0.63  fof(f166,plain,(
% 2.15/0.63    ~r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2)),
% 2.15/0.63    inference(resolution,[],[f163,f42])).
% 2.15/0.63  fof(f42,plain,(
% 2.15/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.15/0.63    inference(cnf_transformation,[],[f2])).
% 2.15/0.63  fof(f2,axiom,(
% 2.15/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.15/0.63  fof(f163,plain,(
% 2.15/0.63    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.15/0.63    inference(resolution,[],[f155,f51])).
% 2.15/0.63  fof(f51,plain,(
% 2.15/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.15/0.63    inference(equality_resolution,[],[f41])).
% 2.15/0.63  fof(f41,plain,(
% 2.15/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.15/0.63    inference(cnf_transformation,[],[f2])).
% 2.15/0.63  fof(f155,plain,(
% 2.15/0.63    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | r1_tarski(X0,sK1)) )),
% 2.15/0.63    inference(superposition,[],[f64,f150])).
% 2.15/0.63  fof(f150,plain,(
% 2.15/0.63    sK1 = k2_xboole_0(k2_relat_1(sK2),sK1)),
% 2.15/0.63    inference(resolution,[],[f148,f126])).
% 2.15/0.63  fof(f126,plain,(
% 2.15/0.63    ( ! [X1] : (~v5_relat_1(sK2,X1) | k2_xboole_0(k2_relat_1(sK2),X1) = X1) )),
% 2.15/0.63    inference(resolution,[],[f121,f39])).
% 2.15/0.63  fof(f121,plain,(
% 2.15/0.63    ( ! [X3] : (r1_tarski(k2_relat_1(sK2),X3) | ~v5_relat_1(sK2,X3)) )),
% 2.15/0.63    inference(resolution,[],[f38,f70])).
% 2.15/0.63  fof(f148,plain,(
% 2.15/0.63    v5_relat_1(sK2,sK1)),
% 2.15/0.63    inference(resolution,[],[f50,f29])).
% 2.15/0.63  fof(f267,plain,(
% 2.15/0.63    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relat_1(sK2)),
% 2.15/0.63    inference(backward_demodulation,[],[f28,f265])).
% 2.15/0.63  fof(f265,plain,(
% 2.15/0.63    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.15/0.63    inference(resolution,[],[f46,f29])).
% 2.15/0.63  fof(f46,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f24])).
% 2.15/0.63  fof(f24,plain,(
% 2.15/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.63    inference(ennf_transformation,[],[f14])).
% 2.15/0.63  fof(f14,axiom,(
% 2.15/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.15/0.63  fof(f28,plain,(
% 2.15/0.63    ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 2.15/0.63    inference(cnf_transformation,[],[f18])).
% 2.15/0.63  fof(f1398,plain,(
% 2.15/0.63    r1_tarski(sK1,k1_relat_1(sK2))),
% 2.15/0.63    inference(forward_demodulation,[],[f1390,f996])).
% 2.15/0.63  fof(f996,plain,(
% 2.15/0.63    sK1 = k1_relset_1(k1_relat_1(sK2),sK1,k6_relat_1(sK1))),
% 2.15/0.63    inference(forward_demodulation,[],[f979,f31])).
% 2.15/0.63  fof(f31,plain,(
% 2.15/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.15/0.63    inference(cnf_transformation,[],[f10])).
% 2.15/0.63  fof(f979,plain,(
% 2.15/0.63    k1_relat_1(k6_relat_1(sK1)) = k1_relset_1(k1_relat_1(sK2),sK1,k6_relat_1(sK1))),
% 2.15/0.63    inference(resolution,[],[f456,f713])).
% 2.15/0.63  fof(f713,plain,(
% 2.15/0.63    r1_tarski(k6_relat_1(sK1),k2_zfmisc_1(k1_relat_1(sK2),sK1))),
% 2.15/0.63    inference(superposition,[],[f703,f328])).
% 2.15/0.63  fof(f328,plain,(
% 2.15/0.63    k2_zfmisc_1(k1_relat_1(sK2),sK1) = k2_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK1))),
% 2.15/0.63    inference(backward_demodulation,[],[f95,f325])).
% 2.15/0.63  fof(f703,plain,(
% 2.15/0.63    ( ! [X0] : (r1_tarski(k6_relat_1(sK1),k2_xboole_0(sK2,X0))) )),
% 2.15/0.63    inference(superposition,[],[f697,f36])).
% 2.15/0.63  fof(f697,plain,(
% 2.15/0.63    ( ! [X0] : (r1_tarski(k6_relat_1(sK1),k2_xboole_0(X0,sK2))) )),
% 2.15/0.63    inference(resolution,[],[f692,f51])).
% 2.15/0.63  fof(f692,plain,(
% 2.15/0.63    ( ! [X4,X5] : (~r1_tarski(X5,k6_relat_1(sK1)) | r1_tarski(X5,k2_xboole_0(X4,sK2))) )),
% 2.15/0.63    inference(superposition,[],[f64,f632])).
% 2.15/0.63  fof(f632,plain,(
% 2.15/0.63    ( ! [X37] : (k2_xboole_0(X37,sK2) = k2_xboole_0(k6_relat_1(sK1),k2_xboole_0(X37,sK2))) )),
% 2.15/0.63    inference(resolution,[],[f63,f30])).
% 2.15/0.63  fof(f63,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X2,X1) = k2_xboole_0(X0,k2_xboole_0(X2,X1))) )),
% 2.15/0.63    inference(resolution,[],[f45,f39])).
% 2.15/0.63  fof(f456,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.15/0.63    inference(resolution,[],[f47,f43])).
% 2.15/0.63  fof(f1390,plain,(
% 2.15/0.63    r1_tarski(k1_relset_1(k1_relat_1(sK2),sK1,k6_relat_1(sK1)),k1_relat_1(sK2))),
% 2.15/0.63    inference(resolution,[],[f1099,f713])).
% 2.15/0.63  fof(f1099,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | r1_tarski(k1_relset_1(X0,X1,X2),X0)) )),
% 2.15/0.63    inference(resolution,[],[f519,f43])).
% 2.15/0.63  fof(f519,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relset_1(X1,X2,X0),X1)) )),
% 2.15/0.63    inference(resolution,[],[f48,f44])).
% 2.15/0.63  fof(f44,plain,(
% 2.15/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.15/0.63    inference(cnf_transformation,[],[f5])).
% 2.15/0.63  fof(f48,plain,(
% 2.15/0.63    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.15/0.63    inference(cnf_transformation,[],[f26])).
% 2.15/0.63  fof(f26,plain,(
% 2.15/0.63    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.15/0.63    inference(ennf_transformation,[],[f12])).
% 2.15/0.63  fof(f12,axiom,(
% 2.15/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.15/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 2.15/0.63  % SZS output end Proof for theBenchmark
% 2.15/0.63  % (27278)------------------------------
% 2.15/0.63  % (27278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.63  % (27278)Termination reason: Refutation
% 2.15/0.63  
% 2.15/0.63  % (27278)Memory used [KB]: 2558
% 2.15/0.63  % (27278)Time elapsed: 0.205 s
% 2.15/0.63  % (27278)------------------------------
% 2.15/0.63  % (27278)------------------------------
% 2.15/0.63  % (27258)Success in time 0.272 s
%------------------------------------------------------------------------------

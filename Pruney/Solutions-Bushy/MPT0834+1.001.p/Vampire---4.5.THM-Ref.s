%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0834+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:44 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  106 (1495 expanded)
%              Number of leaves         :   14 ( 345 expanded)
%              Depth                    :   30
%              Number of atoms          :  278 (4175 expanded)
%              Number of equality atoms :   85 (1293 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1259,plain,(
    $false ),
    inference(resolution,[],[f1246,f1234])).

fof(f1234,plain,(
    r2_hidden(sK10(sK2,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f1230,f341])).

fof(f341,plain,(
    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f102,f329])).

fof(f329,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(resolution,[],[f316,f298])).

fof(f298,plain,
    ( r2_hidden(sK13(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | r2_hidden(sK13(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(resolution,[],[f289,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK15(X0,X1),sK13(X0,X1)),X0)
      | r2_hidden(sK13(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f289,plain,(
    ! [X9] :
      ( ~ r2_hidden(k4_tarski(sK15(sK2,k9_relat_1(sK2,sK0)),X9),sK2)
      | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ) ),
    inference(resolution,[],[f278,f107])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(condensation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f96,f82])).

fof(f82,plain,(
    ! [X3] :
      ( m1_subset_1(X3,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f32,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f81,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f81,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f32,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK15(sK2,k9_relat_1(sK2,X0)),X1),k2_zfmisc_1(X0,X2))
      | k2_relat_1(sK2) = k9_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f277,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f277,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK15(sK2,k9_relat_1(sK2,X2)),X2)
      | k2_relat_1(sK2) = k9_relat_1(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f270,f265])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK13(sK2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,X1))
      | k2_relat_1(sK2) = k9_relat_1(sK2,X0)
      | ~ r2_hidden(sK15(sK2,k9_relat_1(sK2,X0)),X0) ) ),
    inference(resolution,[],[f259,f91])).

fof(f91,plain,(
    ! [X19,X20] :
      ( r2_hidden(k4_tarski(sK4(sK2,X19,X20),X20),sK2)
      | ~ r2_hidden(X20,k9_relat_1(sK2,X19)) ) ),
    inference(resolution,[],[f80,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f80,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f32,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f259,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X5,sK13(sK2,k9_relat_1(sK2,X4))),sK2)
      | ~ r2_hidden(sK15(sK2,k9_relat_1(sK2,X4)),X4)
      | k2_relat_1(sK2) = k9_relat_1(sK2,X4) ) ),
    inference(subsumption_resolution,[],[f258,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK13(X0,X1),X1)
      | ~ r2_hidden(k4_tarski(X3,sK13(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f258,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK15(sK2,k9_relat_1(sK2,X4)),X4)
      | ~ r2_hidden(k4_tarski(X5,sK13(sK2,k9_relat_1(sK2,X4))),sK2)
      | k2_relat_1(sK2) = k9_relat_1(sK2,X4)
      | r2_hidden(sK13(sK2,k9_relat_1(sK2,X4)),k9_relat_1(sK2,X4)) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK15(sK2,k9_relat_1(sK2,X4)),X4)
      | ~ r2_hidden(k4_tarski(X5,sK13(sK2,k9_relat_1(sK2,X4))),sK2)
      | k2_relat_1(sK2) = k9_relat_1(sK2,X4)
      | r2_hidden(sK13(sK2,k9_relat_1(sK2,X4)),k9_relat_1(sK2,X4))
      | k2_relat_1(sK2) = k9_relat_1(sK2,X4) ) ),
    inference(resolution,[],[f99,f54])).

fof(f99,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(k4_tarski(X7,sK13(X9,k9_relat_1(sK2,X8))),sK2)
      | ~ r2_hidden(X7,X8)
      | ~ r2_hidden(k4_tarski(X10,sK13(X9,k9_relat_1(sK2,X8))),X9)
      | k9_relat_1(sK2,X8) = k2_relat_1(X9) ) ),
    inference(resolution,[],[f89,f55])).

fof(f89,plain,(
    ! [X14,X15,X16] :
      ( r2_hidden(X15,k9_relat_1(sK2,X16))
      | ~ r2_hidden(X14,X16)
      | ~ r2_hidden(k4_tarski(X14,X15),sK2) ) ),
    inference(resolution,[],[f80,f66])).

fof(f66,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f270,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK15(sK2,k9_relat_1(sK2,X2)),X2)
      | k2_relat_1(sK2) = k9_relat_1(sK2,X2)
      | r2_hidden(sK13(sK2,k9_relat_1(sK2,X2)),k9_relat_1(sK2,X2)) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK15(sK2,k9_relat_1(sK2,X2)),X2)
      | k2_relat_1(sK2) = k9_relat_1(sK2,X2)
      | r2_hidden(sK13(sK2,k9_relat_1(sK2,X2)),k9_relat_1(sK2,X2))
      | k2_relat_1(sK2) = k9_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f259,f54])).

fof(f316,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK13(sK2,k9_relat_1(sK2,sK0)),k9_relat_1(sK2,X0))
      | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ) ),
    inference(resolution,[],[f314,f91])).

fof(f314,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK13(sK2,k9_relat_1(sK2,sK0))),sK2)
      | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,(
    ! [X0] :
      ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
      | ~ r2_hidden(k4_tarski(X0,sK13(sK2,k9_relat_1(sK2,sK0))),sK2)
      | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ) ),
    inference(resolution,[],[f298,f55])).

fof(f102,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f101,f79])).

fof(f79,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f32,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | k2_relat_1(sK2) != k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f100,f76])).

fof(f76,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f32,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f100,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f95,f77])).

fof(f77,plain,(
    ! [X1] : k7_relset_1(sK0,sK1,sK2,X1) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f32,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f95,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(backward_demodulation,[],[f31,f78])).

fof(f78,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f32,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f31,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f1230,plain,
    ( r2_hidden(sK10(sK2,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,sK1))
    | k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(resolution,[],[f1228,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X1),sK12(X0,X1)),X0)
      | r2_hidden(sK10(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1228,plain,(
    ! [X9] : ~ r2_hidden(k4_tarski(X9,sK12(sK2,k10_relat_1(sK2,sK1))),sK2) ),
    inference(subsumption_resolution,[],[f1223,f341])).

fof(f1223,plain,(
    ! [X9] :
      ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
      | ~ r2_hidden(k4_tarski(X9,sK12(sK2,k10_relat_1(sK2,sK1))),sK2) ) ),
    inference(resolution,[],[f1187,f107])).

fof(f1187,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X4,sK12(sK2,k10_relat_1(sK2,X3))),k2_zfmisc_1(X5,X3))
      | k1_relat_1(sK2) = k10_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f1185,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1185,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK12(sK2,k10_relat_1(sK2,X2)),X2)
      | k1_relat_1(sK2) = k10_relat_1(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f513,f508])).

fof(f508,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(sK2,k10_relat_1(sK2,X0)),k10_relat_1(sK2,X1))
      | k10_relat_1(sK2,X0) = k1_relat_1(sK2)
      | ~ r2_hidden(sK12(sK2,k10_relat_1(sK2,X0)),X0) ) ),
    inference(resolution,[],[f308,f94])).

fof(f94,plain,(
    ! [X26,X27] :
      ( r2_hidden(k4_tarski(X26,sK7(sK2,X27,X26)),sK2)
      | ~ r2_hidden(X26,k10_relat_1(sK2,X27)) ) ),
    inference(resolution,[],[f80,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK7(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK7(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f308,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK10(sK2,k10_relat_1(sK2,X4)),X5),sK2)
      | ~ r2_hidden(sK12(sK2,k10_relat_1(sK2,X4)),X4)
      | k1_relat_1(sK2) = k10_relat_1(sK2,X4) ) ),
    inference(subsumption_resolution,[],[f307,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f307,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK12(sK2,k10_relat_1(sK2,X4)),X4)
      | ~ r2_hidden(k4_tarski(sK10(sK2,k10_relat_1(sK2,X4)),X5),sK2)
      | k1_relat_1(sK2) = k10_relat_1(sK2,X4)
      | r2_hidden(sK10(sK2,k10_relat_1(sK2,X4)),k10_relat_1(sK2,X4)) ) ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK12(sK2,k10_relat_1(sK2,X4)),X4)
      | ~ r2_hidden(k4_tarski(sK10(sK2,k10_relat_1(sK2,X4)),X5),sK2)
      | k1_relat_1(sK2) = k10_relat_1(sK2,X4)
      | r2_hidden(sK10(sK2,k10_relat_1(sK2,X4)),k10_relat_1(sK2,X4))
      | k1_relat_1(sK2) = k10_relat_1(sK2,X4) ) ),
    inference(resolution,[],[f104,f50])).

fof(f104,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(sK10(X5,k10_relat_1(sK2,X4)),X3),sK2)
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(k4_tarski(sK10(X5,k10_relat_1(sK2,X4)),X6),X5)
      | k1_relat_1(X5) = k10_relat_1(sK2,X4) ) ),
    inference(resolution,[],[f92,f51])).

fof(f92,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(X21,k10_relat_1(sK2,X23))
      | ~ r2_hidden(X22,X23)
      | ~ r2_hidden(k4_tarski(X21,X22),sK2) ) ),
    inference(resolution,[],[f80,f69])).

fof(f69,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f513,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK12(sK2,k10_relat_1(sK2,X2)),X2)
      | k1_relat_1(sK2) = k10_relat_1(sK2,X2)
      | r2_hidden(sK10(sK2,k10_relat_1(sK2,X2)),k10_relat_1(sK2,X2)) ) ),
    inference(duplicate_literal_removal,[],[f509])).

fof(f509,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK12(sK2,k10_relat_1(sK2,X2)),X2)
      | k1_relat_1(sK2) = k10_relat_1(sK2,X2)
      | r2_hidden(sK10(sK2,k10_relat_1(sK2,X2)),k10_relat_1(sK2,X2))
      | k1_relat_1(sK2) = k10_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f308,f50])).

fof(f1246,plain,(
    ! [X0] : ~ r2_hidden(sK10(sK2,k10_relat_1(sK2,sK1)),k10_relat_1(sK2,X0)) ),
    inference(resolution,[],[f1245,f94])).

fof(f1245,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK10(sK2,k10_relat_1(sK2,sK1)),X0),sK2) ),
    inference(subsumption_resolution,[],[f1244,f341])).

fof(f1244,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK10(sK2,k10_relat_1(sK2,sK1)),X0),sK2)
      | k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ) ),
    inference(resolution,[],[f1234,f51])).

%------------------------------------------------------------------------------

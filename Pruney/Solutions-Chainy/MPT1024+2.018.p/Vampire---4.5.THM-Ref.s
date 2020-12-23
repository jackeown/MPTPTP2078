%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:14 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 725 expanded)
%              Number of leaves         :   12 ( 135 expanded)
%              Depth                    :   22
%              Number of atoms          :  300 (2933 expanded)
%              Number of equality atoms :   18 ( 417 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(subsumption_resolution,[],[f382,f67])).

fof(f67,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f52,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f382,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f381,f371])).

fof(f371,plain,(
    sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f364,f370])).

fof(f370,plain,(
    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f368,f135])).

fof(f135,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f70,f128])).

fof(f128,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f89,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f89,plain,(
    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f83,f67])).

fof(f83,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f81,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f81,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f32,f77])).

fof(f77,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f58,f34])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f32,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f368,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f298,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f298,plain,(
    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f297,f156])).

fof(f156,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(resolution,[],[f78,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f75,f77])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f57,f34])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
      | m1_subset_1(sK4,X0) ) ),
    inference(backward_demodulation,[],[f71,f77])).

fof(f71,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0))
      | m1_subset_1(sK4,X0) ) ),
    inference(resolution,[],[f56,f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f297,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f292,f106])).

fof(f106,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f91,f40])).

fof(f91,plain,(
    r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f85,f67])).

fof(f85,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f81,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f292,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(resolution,[],[f155,f81])).

fof(f155,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) ) ),
    inference(subsumption_resolution,[],[f154,f136])).

fof(f136,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f69,f128])).

fof(f69,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f154,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f153,f34])).

fof(f153,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f146,f135])).

fof(f146,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X5,sK1)
      | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f35,f77])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f364,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) ),
    inference(resolution,[],[f287,f31])).

fof(f31,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f287,plain,(
    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f286,f156])).

fof(f286,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f281,f106])).

fof(f281,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(resolution,[],[f152,f81])).

fof(f152,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2) ) ),
    inference(subsumption_resolution,[],[f151,f136])).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f150,f34])).

fof(f150,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f145,f135])).

fof(f145,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | v1_xboole_0(X2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X3,sK1)
      | r2_hidden(sK5(X2,sK0,sK3,X3),X2)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f37,f77])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK5(X1,X2,X3,X4),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f381,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f374,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f374,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f321,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f321,plain,(
    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(subsumption_resolution,[],[f320,f156])).

fof(f320,plain,
    ( ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(subsumption_resolution,[],[f315,f106])).

fof(f315,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4,sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(resolution,[],[f149,f81])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) ) ),
    inference(subsumption_resolution,[],[f148,f136])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f147,f34])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f144,f135])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X1,sK1)
      | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f36,f77])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:11:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (2735)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (2733)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (2743)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (2741)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (2729)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (2739)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (2731)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.26/0.52  % (2745)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.26/0.53  % (2728)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (2736)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.26/0.53  % (2744)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.26/0.53  % (2727)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.26/0.53  % (2740)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.49/0.54  % (2730)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.49/0.54  % (2742)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.49/0.55  % (2732)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.49/0.55  % (2734)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.49/0.55  % (2744)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.56  % (2738)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.49/0.56  % (2747)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.49/0.56  % (2747)Refutation not found, incomplete strategy% (2747)------------------------------
% 1.49/0.56  % (2747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (2737)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.49/0.56  % (2747)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (2747)Memory used [KB]: 10618
% 1.49/0.56  % (2747)Time elapsed: 0.085 s
% 1.49/0.56  % (2747)------------------------------
% 1.49/0.56  % (2747)------------------------------
% 1.49/0.57  % (2746)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.49/0.57  % SZS output start Proof for theBenchmark
% 1.49/0.57  fof(f383,plain,(
% 1.49/0.57    $false),
% 1.49/0.57    inference(subsumption_resolution,[],[f382,f67])).
% 1.49/0.57  fof(f67,plain,(
% 1.49/0.57    v1_relat_1(sK3)),
% 1.49/0.57    inference(resolution,[],[f52,f34])).
% 1.49/0.57  fof(f34,plain,(
% 1.49/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.57    inference(cnf_transformation,[],[f17])).
% 1.49/0.57  fof(f17,plain,(
% 1.49/0.57    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.49/0.57    inference(flattening,[],[f16])).
% 1.49/0.57  fof(f16,plain,(
% 1.49/0.57    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.49/0.57    inference(ennf_transformation,[],[f15])).
% 1.49/0.57  fof(f15,plain,(
% 1.49/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.49/0.57    inference(pure_predicate_removal,[],[f14])).
% 1.49/0.57  fof(f14,negated_conjecture,(
% 1.49/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.49/0.57    inference(negated_conjecture,[],[f13])).
% 1.49/0.57  fof(f13,conjecture,(
% 1.49/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 1.49/0.57  fof(f52,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f24])).
% 1.49/0.57  fof(f24,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.57    inference(ennf_transformation,[],[f7])).
% 1.49/0.57  fof(f7,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.49/0.57  fof(f382,plain,(
% 1.49/0.57    ~v1_relat_1(sK3)),
% 1.49/0.57    inference(subsumption_resolution,[],[f381,f371])).
% 1.49/0.57  fof(f371,plain,(
% 1.49/0.57    sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))),
% 1.49/0.57    inference(subsumption_resolution,[],[f364,f370])).
% 1.49/0.57  fof(f370,plain,(
% 1.49/0.57    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)),
% 1.49/0.57    inference(subsumption_resolution,[],[f368,f135])).
% 1.49/0.57  fof(f135,plain,(
% 1.49/0.57    ~v1_xboole_0(sK0)),
% 1.49/0.57    inference(subsumption_resolution,[],[f70,f128])).
% 1.49/0.57  fof(f128,plain,(
% 1.49/0.57    ~v1_xboole_0(sK3)),
% 1.49/0.57    inference(resolution,[],[f89,f40])).
% 1.49/0.57  fof(f40,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f1])).
% 1.49/0.57  fof(f1,axiom,(
% 1.49/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.49/0.57  fof(f89,plain,(
% 1.49/0.57    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 1.49/0.57    inference(subsumption_resolution,[],[f83,f67])).
% 1.49/0.57  fof(f83,plain,(
% 1.49/0.57    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 1.49/0.57    inference(resolution,[],[f81,f49])).
% 1.49/0.57  fof(f49,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f23])).
% 1.49/0.57  fof(f23,plain,(
% 1.49/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.49/0.57    inference(ennf_transformation,[],[f5])).
% 1.49/0.57  fof(f5,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.49/0.57  fof(f81,plain,(
% 1.49/0.57    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.49/0.57    inference(backward_demodulation,[],[f32,f77])).
% 1.49/0.57  fof(f77,plain,(
% 1.49/0.57    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.49/0.57    inference(resolution,[],[f58,f34])).
% 1.49/0.57  fof(f58,plain,(
% 1.49/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f30])).
% 1.49/0.57  fof(f30,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.57    inference(ennf_transformation,[],[f11])).
% 1.49/0.57  fof(f11,axiom,(
% 1.49/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.49/0.57  fof(f32,plain,(
% 1.49/0.57    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.49/0.57    inference(cnf_transformation,[],[f17])).
% 1.49/0.57  fof(f70,plain,(
% 1.49/0.57    ~v1_xboole_0(sK0) | v1_xboole_0(sK3)),
% 1.49/0.57    inference(resolution,[],[f46,f34])).
% 1.49/0.57  fof(f46,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f21])).
% 1.49/0.57  fof(f21,plain,(
% 1.49/0.57    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f8])).
% 1.49/0.57  fof(f8,axiom,(
% 1.49/0.57    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.49/0.57  fof(f368,plain,(
% 1.49/0.57    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) | v1_xboole_0(sK0)),
% 1.49/0.57    inference(resolution,[],[f298,f44])).
% 1.49/0.57  fof(f44,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f19])).
% 1.49/0.57  fof(f19,plain,(
% 1.49/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f2])).
% 1.49/0.57  fof(f2,axiom,(
% 1.49/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.49/0.57  fof(f298,plain,(
% 1.49/0.57    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 1.49/0.57    inference(subsumption_resolution,[],[f297,f156])).
% 1.49/0.57  fof(f156,plain,(
% 1.49/0.57    m1_subset_1(sK4,sK1)),
% 1.49/0.57    inference(resolution,[],[f78,f82])).
% 1.49/0.57  fof(f82,plain,(
% 1.49/0.57    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.49/0.57    inference(backward_demodulation,[],[f75,f77])).
% 1.49/0.57  fof(f75,plain,(
% 1.49/0.57    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.49/0.57    inference(resolution,[],[f57,f34])).
% 1.49/0.57  fof(f57,plain,(
% 1.49/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f29])).
% 1.49/0.57  fof(f29,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.57    inference(ennf_transformation,[],[f10])).
% 1.49/0.57  fof(f10,axiom,(
% 1.49/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.49/0.57  fof(f78,plain,(
% 1.49/0.57    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) )),
% 1.49/0.57    inference(backward_demodulation,[],[f71,f77])).
% 1.49/0.57  fof(f71,plain,(
% 1.49/0.57    ( ! [X0] : (~m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0)) | m1_subset_1(sK4,X0)) )),
% 1.49/0.57    inference(resolution,[],[f56,f32])).
% 1.49/0.57  fof(f56,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f28])).
% 1.49/0.57  fof(f28,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.49/0.57    inference(flattening,[],[f27])).
% 1.49/0.57  fof(f27,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.49/0.57    inference(ennf_transformation,[],[f4])).
% 1.49/0.57  fof(f4,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.49/0.57  fof(f297,plain,(
% 1.49/0.57    ~m1_subset_1(sK4,sK1) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 1.49/0.57    inference(subsumption_resolution,[],[f292,f106])).
% 1.49/0.57  fof(f106,plain,(
% 1.49/0.57    ~v1_xboole_0(sK2)),
% 1.49/0.57    inference(resolution,[],[f91,f40])).
% 1.49/0.57  fof(f91,plain,(
% 1.49/0.57    r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 1.49/0.57    inference(subsumption_resolution,[],[f85,f67])).
% 1.49/0.57  fof(f85,plain,(
% 1.49/0.57    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 1.49/0.57    inference(resolution,[],[f81,f50])).
% 1.49/0.57  fof(f50,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f23])).
% 1.49/0.57  fof(f292,plain,(
% 1.49/0.57    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 1.49/0.57    inference(resolution,[],[f155,f81])).
% 1.49/0.57  fof(f155,plain,(
% 1.49/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f154,f136])).
% 1.49/0.57  fof(f136,plain,(
% 1.49/0.57    ~v1_xboole_0(sK1)),
% 1.49/0.57    inference(subsumption_resolution,[],[f69,f128])).
% 1.49/0.57  fof(f69,plain,(
% 1.49/0.57    ~v1_xboole_0(sK1) | v1_xboole_0(sK3)),
% 1.49/0.57    inference(resolution,[],[f45,f34])).
% 1.49/0.57  fof(f45,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f20])).
% 1.49/0.57  fof(f20,plain,(
% 1.49/0.57    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f9])).
% 1.49/0.57  fof(f9,axiom,(
% 1.49/0.57    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.49/0.57  fof(f154,plain,(
% 1.49/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f153,f34])).
% 1.49/0.57  fof(f153,plain,(
% 1.49/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f146,f135])).
% 1.49/0.57  fof(f146,plain,(
% 1.49/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X5,sK1) | m1_subset_1(sK5(X4,sK0,sK3,X5),sK0) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(superposition,[],[f35,f77])).
% 1.49/0.57  fof(f35,plain,(
% 1.49/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | v1_xboole_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f18])).
% 1.49/0.57  fof(f18,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f12])).
% 1.49/0.57  fof(f12,axiom,(
% 1.49/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 1.49/0.57  fof(f364,plain,(
% 1.49/0.57    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) | sK4 != k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))),
% 1.49/0.57    inference(resolution,[],[f287,f31])).
% 1.49/0.57  fof(f31,plain,(
% 1.49/0.57    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f17])).
% 1.49/0.57  fof(f287,plain,(
% 1.49/0.57    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 1.49/0.57    inference(subsumption_resolution,[],[f286,f156])).
% 1.49/0.57  fof(f286,plain,(
% 1.49/0.57    ~m1_subset_1(sK4,sK1) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 1.49/0.57    inference(subsumption_resolution,[],[f281,f106])).
% 1.49/0.57  fof(f281,plain,(
% 1.49/0.57    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 1.49/0.57    inference(resolution,[],[f152,f81])).
% 1.49/0.57  fof(f152,plain,(
% 1.49/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f151,f136])).
% 1.49/0.57  fof(f151,plain,(
% 1.49/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f150,f34])).
% 1.49/0.57  fof(f150,plain,(
% 1.49/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f145,f135])).
% 1.49/0.57  fof(f145,plain,(
% 1.49/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X3,sK1) | r2_hidden(sK5(X2,sK0,sK3,X3),X2) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(superposition,[],[f37,f77])).
% 1.49/0.57  fof(f37,plain,(
% 1.49/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK5(X1,X2,X3,X4),X1) | v1_xboole_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f18])).
% 1.49/0.57  fof(f381,plain,(
% 1.49/0.57    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3)),
% 1.49/0.57    inference(subsumption_resolution,[],[f374,f33])).
% 1.49/0.57  fof(f33,plain,(
% 1.49/0.57    v1_funct_1(sK3)),
% 1.49/0.57    inference(cnf_transformation,[],[f17])).
% 1.49/0.57  fof(f374,plain,(
% 1.49/0.57    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3)),
% 1.49/0.57    inference(resolution,[],[f321,f54])).
% 1.49/0.57  fof(f54,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f26])).
% 1.49/0.57  fof(f26,plain,(
% 1.49/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.49/0.57    inference(flattening,[],[f25])).
% 1.49/0.57  fof(f25,plain,(
% 1.49/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.49/0.57    inference(ennf_transformation,[],[f6])).
% 1.49/0.57  fof(f6,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.49/0.57  fof(f321,plain,(
% 1.49/0.57    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 1.49/0.57    inference(subsumption_resolution,[],[f320,f156])).
% 1.49/0.57  fof(f320,plain,(
% 1.49/0.57    ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 1.49/0.57    inference(subsumption_resolution,[],[f315,f106])).
% 1.49/0.57  fof(f315,plain,(
% 1.49/0.57    v1_xboole_0(sK2) | ~m1_subset_1(sK4,sK1) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 1.49/0.57    inference(resolution,[],[f149,f81])).
% 1.49/0.57  fof(f149,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f148,f136])).
% 1.49/0.57  fof(f148,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f147,f34])).
% 1.49/0.57  fof(f147,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f144,f135])).
% 1.49/0.57  fof(f144,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | v1_xboole_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(sK1)) )),
% 1.49/0.57    inference(superposition,[],[f36,f77])).
% 1.49/0.57  fof(f36,plain,(
% 1.49/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | v1_xboole_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f18])).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (2744)------------------------------
% 1.49/0.57  % (2744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (2744)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (2744)Memory used [KB]: 1918
% 1.49/0.57  % (2744)Time elapsed: 0.118 s
% 1.49/0.57  % (2744)------------------------------
% 1.49/0.57  % (2744)------------------------------
% 1.49/0.57  % (2726)Success in time 0.215 s
%------------------------------------------------------------------------------

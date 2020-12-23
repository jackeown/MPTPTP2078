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
% DateTime   : Thu Dec  3 13:07:59 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 287 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   20
%              Number of atoms          :  270 (1002 expanded)
%              Number of equality atoms :   61 ( 209 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(subsumption_resolution,[],[f418,f186])).

fof(f186,plain,(
    ! [X1] : ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f185,f88])).

fof(f88,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f47,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f185,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f182,f87])).

fof(f87,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f46,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f182,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0))
      | r2_hidden(k4_tarski(sK5(X1,k1_relat_1(k1_xboole_0),k1_xboole_0),X1),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f60,f98])).

fof(f98,plain,(
    k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f45,f88])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f418,plain,(
    r2_hidden(sK0,k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f400,f75])).

fof(f400,plain,(
    r2_hidden(sK0,k2_relat_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f153,f395])).

fof(f395,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f383,f380])).

fof(f380,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f204,f369])).

fof(f369,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f368,f130])).

fof(f130,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f368,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f367,f42])).

fof(f367,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f71,f41])).

fof(f41,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f204,plain,(
    r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f203,f93])).

fof(f93,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f203,plain,
    ( r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f199,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f199,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f197,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f197,plain,(
    r2_hidden(k4_tarski(sK5(sK0,k1_relat_1(sK3),sK3),sK0),sK3) ),
    inference(resolution,[],[f184,f143])).

fof(f143,plain,(
    r2_hidden(sK0,k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f43,f138])).

fof(f138,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f65,f42])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f43,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f184,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(k4_tarski(sK5(X0,k1_relat_1(sK3),sK3),X0),sK3) ) ),
    inference(subsumption_resolution,[],[f181,f93])).

fof(f181,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(k4_tarski(sK5(X0,k1_relat_1(sK3),sK3),X0),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f60,f99])).

fof(f99,plain,(
    k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(resolution,[],[f93,f45])).

fof(f383,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f208,f369])).

fof(f208,plain,(
    ~ r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),sK1) ),
    inference(resolution,[],[f207,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f207,plain,(
    ~ m1_subset_1(sK5(sK0,k1_relat_1(sK3),sK3),sK1) ),
    inference(trivial_inequality_removal,[],[f206])).

fof(f206,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK5(sK0,k1_relat_1(sK3),sK3),sK1) ),
    inference(superposition,[],[f39,f202])).

fof(f202,plain,(
    sK0 = k1_funct_1(sK3,sK5(sK0,k1_relat_1(sK3),sK3)) ),
    inference(subsumption_resolution,[],[f201,f93])).

fof(f201,plain,
    ( sK0 = k1_funct_1(sK3,sK5(sK0,k1_relat_1(sK3),sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f198,f40])).

fof(f198,plain,
    ( ~ v1_funct_1(sK3)
    | sK0 = k1_funct_1(sK3,sK5(sK0,k1_relat_1(sK3),sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f197,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f39,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f153,plain,(
    r2_hidden(sK0,k2_relat_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f151,f47])).

fof(f151,plain,
    ( r2_hidden(sK0,k2_relat_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f148,f42])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | r2_hidden(sK0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f146,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,k2_relat_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v5_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f92])).

fof(f92,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | v5_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

fof(f146,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,X0)
      | r2_hidden(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f144,f93])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3)
      | r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f143,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:10:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (25707)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (25723)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (25715)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (25713)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (25711)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (25736)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (25722)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (25730)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (25734)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (25712)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (25709)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (25710)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (25729)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (25727)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (25717)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (25714)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (25717)Refutation not found, incomplete strategy% (25717)------------------------------
% 0.22/0.55  % (25717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (25717)Memory used [KB]: 10746
% 0.22/0.55  % (25717)Time elapsed: 0.133 s
% 0.22/0.55  % (25717)------------------------------
% 0.22/0.55  % (25717)------------------------------
% 0.22/0.55  % (25728)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (25721)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (25719)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (25726)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (25720)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (25718)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (25733)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (25731)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.56  % (25735)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.56  % (25725)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.58  % (25732)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.58  % (25729)Refutation not found, incomplete strategy% (25729)------------------------------
% 1.32/0.58  % (25729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.58  % (25729)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.58  
% 1.32/0.58  % (25729)Memory used [KB]: 10874
% 1.32/0.58  % (25729)Time elapsed: 0.167 s
% 1.32/0.58  % (25729)------------------------------
% 1.32/0.58  % (25729)------------------------------
% 1.32/0.58  % (25713)Refutation found. Thanks to Tanya!
% 1.32/0.58  % SZS status Theorem for theBenchmark
% 1.32/0.58  % SZS output start Proof for theBenchmark
% 1.32/0.58  fof(f419,plain,(
% 1.32/0.58    $false),
% 1.32/0.58    inference(subsumption_resolution,[],[f418,f186])).
% 1.32/0.58  fof(f186,plain,(
% 1.32/0.58    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(k1_xboole_0))) )),
% 1.32/0.58    inference(subsumption_resolution,[],[f185,f88])).
% 1.32/0.58  fof(f88,plain,(
% 1.32/0.58    v1_relat_1(k1_xboole_0)),
% 1.32/0.58    inference(superposition,[],[f47,f75])).
% 1.32/0.58  fof(f75,plain,(
% 1.32/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.32/0.58    inference(equality_resolution,[],[f58])).
% 1.32/0.58  fof(f58,plain,(
% 1.32/0.58    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f4])).
% 1.32/0.58  fof(f4,axiom,(
% 1.32/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.32/0.58  fof(f47,plain,(
% 1.32/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.32/0.58    inference(cnf_transformation,[],[f8])).
% 1.32/0.58  fof(f8,axiom,(
% 1.32/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.32/0.58  fof(f185,plain,(
% 1.32/0.58    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 1.32/0.58    inference(subsumption_resolution,[],[f182,f87])).
% 1.32/0.58  fof(f87,plain,(
% 1.32/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.58    inference(resolution,[],[f46,f44])).
% 1.32/0.58  fof(f44,plain,(
% 1.32/0.58    v1_xboole_0(k1_xboole_0)),
% 1.32/0.58    inference(cnf_transformation,[],[f3])).
% 1.32/0.58  fof(f3,axiom,(
% 1.32/0.58    v1_xboole_0(k1_xboole_0)),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.32/0.58  fof(f46,plain,(
% 1.32/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f23])).
% 1.32/0.58  fof(f23,plain,(
% 1.32/0.58    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.32/0.58    inference(ennf_transformation,[],[f19])).
% 1.32/0.58  fof(f19,plain,(
% 1.32/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.32/0.58    inference(unused_predicate_definition_removal,[],[f1])).
% 1.32/0.58  fof(f1,axiom,(
% 1.32/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.32/0.58  fof(f182,plain,(
% 1.32/0.58    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(k1_xboole_0)) | r2_hidden(k4_tarski(sK5(X1,k1_relat_1(k1_xboole_0),k1_xboole_0),X1),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.32/0.58    inference(superposition,[],[f60,f98])).
% 1.32/0.58  fof(f98,plain,(
% 1.32/0.58    k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0)),
% 1.32/0.58    inference(resolution,[],[f45,f88])).
% 1.32/0.58  fof(f45,plain,(
% 1.32/0.58    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f22])).
% 1.32/0.58  fof(f22,plain,(
% 1.32/0.58    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.58    inference(ennf_transformation,[],[f10])).
% 1.32/0.58  fof(f10,axiom,(
% 1.32/0.58    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.32/0.58  fof(f60,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f31])).
% 1.32/0.58  fof(f31,plain,(
% 1.32/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.32/0.58    inference(ennf_transformation,[],[f9])).
% 1.32/0.58  fof(f9,axiom,(
% 1.32/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.32/0.58  fof(f418,plain,(
% 1.32/0.58    r2_hidden(sK0,k2_relat_1(k1_xboole_0))),
% 1.32/0.58    inference(forward_demodulation,[],[f400,f75])).
% 1.32/0.58  fof(f400,plain,(
% 1.32/0.58    r2_hidden(sK0,k2_relat_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.32/0.58    inference(backward_demodulation,[],[f153,f395])).
% 1.32/0.58  fof(f395,plain,(
% 1.32/0.58    k1_xboole_0 = sK2),
% 1.32/0.58    inference(subsumption_resolution,[],[f383,f380])).
% 1.32/0.58  fof(f380,plain,(
% 1.32/0.58    r2_hidden(sK5(sK0,sK1,sK3),sK1) | k1_xboole_0 = sK2),
% 1.32/0.58    inference(superposition,[],[f204,f369])).
% 1.32/0.58  fof(f369,plain,(
% 1.32/0.58    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.32/0.58    inference(superposition,[],[f368,f130])).
% 1.32/0.58  fof(f130,plain,(
% 1.32/0.58    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.32/0.58    inference(resolution,[],[f64,f42])).
% 1.32/0.58  fof(f42,plain,(
% 1.32/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.32/0.58    inference(cnf_transformation,[],[f21])).
% 1.32/0.58  fof(f21,plain,(
% 1.32/0.58    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 1.32/0.58    inference(flattening,[],[f20])).
% 1.32/0.58  fof(f20,plain,(
% 1.32/0.58    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 1.32/0.58    inference(ennf_transformation,[],[f18])).
% 1.32/0.58  fof(f18,negated_conjecture,(
% 1.32/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.32/0.58    inference(negated_conjecture,[],[f17])).
% 1.32/0.58  fof(f17,conjecture,(
% 1.32/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 1.32/0.58  fof(f64,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f33])).
% 1.32/0.58  fof(f33,plain,(
% 1.32/0.58    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.58    inference(ennf_transformation,[],[f14])).
% 1.32/0.58  fof(f14,axiom,(
% 1.32/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.32/0.58  fof(f368,plain,(
% 1.32/0.58    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.32/0.58    inference(subsumption_resolution,[],[f367,f42])).
% 1.32/0.58  fof(f367,plain,(
% 1.32/0.58    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.32/0.58    inference(resolution,[],[f71,f41])).
% 1.32/0.58  fof(f41,plain,(
% 1.32/0.58    v1_funct_2(sK3,sK1,sK2)),
% 1.32/0.58    inference(cnf_transformation,[],[f21])).
% 1.32/0.58  fof(f71,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.58    inference(cnf_transformation,[],[f36])).
% 1.32/0.58  fof(f36,plain,(
% 1.32/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.58    inference(flattening,[],[f35])).
% 1.32/0.58  fof(f35,plain,(
% 1.32/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.58    inference(ennf_transformation,[],[f16])).
% 1.32/0.58  fof(f16,axiom,(
% 1.32/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.32/0.58  fof(f204,plain,(
% 1.32/0.58    r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))),
% 1.32/0.58    inference(subsumption_resolution,[],[f203,f93])).
% 1.32/0.58  fof(f93,plain,(
% 1.32/0.58    v1_relat_1(sK3)),
% 1.32/0.58    inference(resolution,[],[f63,f42])).
% 1.32/0.58  fof(f63,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f32])).
% 1.32/0.58  fof(f32,plain,(
% 1.32/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.58    inference(ennf_transformation,[],[f13])).
% 1.32/0.58  fof(f13,axiom,(
% 1.32/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.32/0.58  fof(f203,plain,(
% 1.32/0.58    r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.32/0.58    inference(subsumption_resolution,[],[f199,f40])).
% 1.32/0.58  fof(f40,plain,(
% 1.32/0.58    v1_funct_1(sK3)),
% 1.32/0.58    inference(cnf_transformation,[],[f21])).
% 1.32/0.58  fof(f199,plain,(
% 1.32/0.58    ~v1_funct_1(sK3) | r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.32/0.58    inference(resolution,[],[f197,f72])).
% 1.32/0.58  fof(f72,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f38])).
% 1.32/0.58  fof(f38,plain,(
% 1.32/0.58    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.32/0.58    inference(flattening,[],[f37])).
% 1.32/0.58  fof(f37,plain,(
% 1.32/0.58    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.32/0.58    inference(ennf_transformation,[],[f12])).
% 1.32/0.58  fof(f12,axiom,(
% 1.32/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.32/0.58  fof(f197,plain,(
% 1.32/0.58    r2_hidden(k4_tarski(sK5(sK0,k1_relat_1(sK3),sK3),sK0),sK3)),
% 1.32/0.58    inference(resolution,[],[f184,f143])).
% 1.32/0.58  fof(f143,plain,(
% 1.32/0.58    r2_hidden(sK0,k2_relat_1(sK3))),
% 1.32/0.58    inference(backward_demodulation,[],[f43,f138])).
% 1.32/0.58  fof(f138,plain,(
% 1.32/0.58    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.32/0.58    inference(resolution,[],[f65,f42])).
% 1.32/0.58  fof(f65,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f34])).
% 1.32/0.58  fof(f34,plain,(
% 1.32/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.58    inference(ennf_transformation,[],[f15])).
% 1.32/0.58  fof(f15,axiom,(
% 1.32/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.32/0.58  fof(f43,plain,(
% 1.32/0.58    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 1.32/0.58    inference(cnf_transformation,[],[f21])).
% 1.32/0.58  fof(f184,plain,(
% 1.32/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK5(X0,k1_relat_1(sK3),sK3),X0),sK3)) )),
% 1.32/0.58    inference(subsumption_resolution,[],[f181,f93])).
% 1.32/0.58  fof(f181,plain,(
% 1.32/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK5(X0,k1_relat_1(sK3),sK3),X0),sK3) | ~v1_relat_1(sK3)) )),
% 1.32/0.58    inference(superposition,[],[f60,f99])).
% 1.32/0.58  fof(f99,plain,(
% 1.32/0.58    k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3)),
% 1.32/0.58    inference(resolution,[],[f93,f45])).
% 1.32/0.58  fof(f383,plain,(
% 1.32/0.58    ~r2_hidden(sK5(sK0,sK1,sK3),sK1) | k1_xboole_0 = sK2),
% 1.32/0.58    inference(superposition,[],[f208,f369])).
% 1.32/0.58  fof(f208,plain,(
% 1.32/0.58    ~r2_hidden(sK5(sK0,k1_relat_1(sK3),sK3),sK1)),
% 1.32/0.58    inference(resolution,[],[f207,f50])).
% 1.32/0.58  fof(f50,plain,(
% 1.32/0.58    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f25])).
% 1.32/0.58  fof(f25,plain,(
% 1.32/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.32/0.58    inference(ennf_transformation,[],[f5])).
% 1.32/0.58  fof(f5,axiom,(
% 1.32/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.32/0.58  fof(f207,plain,(
% 1.32/0.58    ~m1_subset_1(sK5(sK0,k1_relat_1(sK3),sK3),sK1)),
% 1.32/0.58    inference(trivial_inequality_removal,[],[f206])).
% 1.32/0.58  fof(f206,plain,(
% 1.32/0.58    sK0 != sK0 | ~m1_subset_1(sK5(sK0,k1_relat_1(sK3),sK3),sK1)),
% 1.32/0.58    inference(superposition,[],[f39,f202])).
% 1.32/0.58  fof(f202,plain,(
% 1.32/0.58    sK0 = k1_funct_1(sK3,sK5(sK0,k1_relat_1(sK3),sK3))),
% 1.32/0.58    inference(subsumption_resolution,[],[f201,f93])).
% 1.32/0.58  fof(f201,plain,(
% 1.32/0.58    sK0 = k1_funct_1(sK3,sK5(sK0,k1_relat_1(sK3),sK3)) | ~v1_relat_1(sK3)),
% 1.32/0.58    inference(subsumption_resolution,[],[f198,f40])).
% 1.32/0.58  fof(f198,plain,(
% 1.32/0.58    ~v1_funct_1(sK3) | sK0 = k1_funct_1(sK3,sK5(sK0,k1_relat_1(sK3),sK3)) | ~v1_relat_1(sK3)),
% 1.32/0.58    inference(resolution,[],[f197,f73])).
% 1.32/0.58  fof(f73,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f38])).
% 1.32/0.58  fof(f39,plain,(
% 1.32/0.58    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f21])).
% 1.32/0.58  fof(f153,plain,(
% 1.32/0.58    r2_hidden(sK0,k2_relat_1(k2_zfmisc_1(sK1,sK2)))),
% 1.32/0.58    inference(subsumption_resolution,[],[f151,f47])).
% 1.32/0.58  fof(f151,plain,(
% 1.32/0.58    r2_hidden(sK0,k2_relat_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 1.32/0.58    inference(resolution,[],[f148,f42])).
% 1.32/0.58  fof(f148,plain,(
% 1.32/0.58    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | r2_hidden(sK0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.32/0.58    inference(resolution,[],[f146,f120])).
% 1.32/0.58  fof(f120,plain,(
% 1.32/0.58    ( ! [X0,X1] : (v5_relat_1(X1,k2_relat_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.32/0.58    inference(duplicate_literal_removal,[],[f119])).
% 1.32/0.58  fof(f119,plain,(
% 1.32/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v5_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.32/0.58    inference(resolution,[],[f52,f105])).
% 1.32/0.58  fof(f105,plain,(
% 1.32/0.58    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.32/0.58    inference(resolution,[],[f48,f92])).
% 1.32/0.58  fof(f92,plain,(
% 1.32/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.32/0.58    inference(duplicate_literal_removal,[],[f91])).
% 1.32/0.58  fof(f91,plain,(
% 1.32/0.58    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.32/0.58    inference(resolution,[],[f55,f54])).
% 1.32/0.58  fof(f54,plain,(
% 1.32/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f30])).
% 1.32/0.58  fof(f30,plain,(
% 1.32/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.32/0.58    inference(ennf_transformation,[],[f2])).
% 1.32/0.58  fof(f2,axiom,(
% 1.32/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.32/0.58  fof(f55,plain,(
% 1.32/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f30])).
% 1.32/0.58  fof(f48,plain,(
% 1.32/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | v5_relat_1(X1,X0)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f24])).
% 1.32/0.58  fof(f24,plain,(
% 1.32/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.32/0.58    inference(ennf_transformation,[],[f7])).
% 1.32/0.58  fof(f7,axiom,(
% 1.32/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.32/0.58  fof(f52,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | v5_relat_1(X2,X0)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f29])).
% 1.32/0.58  fof(f29,plain,(
% 1.32/0.58    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.32/0.58    inference(flattening,[],[f28])).
% 1.32/0.58  fof(f28,plain,(
% 1.32/0.58    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.32/0.58    inference(ennf_transformation,[],[f6])).
% 1.32/0.58  fof(f6,axiom,(
% 1.32/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).
% 1.32/0.58  fof(f146,plain,(
% 1.32/0.58    ( ! [X0] : (~v5_relat_1(sK3,X0) | r2_hidden(sK0,X0)) )),
% 1.32/0.58    inference(subsumption_resolution,[],[f144,f93])).
% 1.32/0.58  fof(f144,plain,(
% 1.32/0.58    ( ! [X0] : (~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3) | r2_hidden(sK0,X0)) )),
% 1.32/0.58    inference(resolution,[],[f143,f51])).
% 1.32/0.58  fof(f51,plain,(
% 1.32/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | r2_hidden(X2,X0)) )),
% 1.32/0.58    inference(cnf_transformation,[],[f27])).
% 1.32/0.58  fof(f27,plain,(
% 1.32/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.32/0.58    inference(flattening,[],[f26])).
% 1.32/0.58  fof(f26,plain,(
% 1.32/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.32/0.58    inference(ennf_transformation,[],[f11])).
% 1.32/0.58  fof(f11,axiom,(
% 1.32/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 1.32/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).
% 1.32/0.58  % SZS output end Proof for theBenchmark
% 1.32/0.58  % (25713)------------------------------
% 1.32/0.58  % (25713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.58  % (25713)Termination reason: Refutation
% 1.32/0.58  
% 1.32/0.58  % (25713)Memory used [KB]: 6524
% 1.32/0.58  % (25713)Time elapsed: 0.165 s
% 1.32/0.58  % (25713)------------------------------
% 1.32/0.58  % (25713)------------------------------
% 1.32/0.58  % (25706)Success in time 0.213 s
%------------------------------------------------------------------------------

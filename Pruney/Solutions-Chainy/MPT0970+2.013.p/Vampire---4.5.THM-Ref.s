%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 (5034 expanded)
%              Number of leaves         :   12 ( 972 expanded)
%              Depth                    :   37
%              Number of atoms          :  275 (22030 expanded)
%              Number of equality atoms :   97 (6800 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(subsumption_resolution,[],[f323,f33])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f323,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f320,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f320,plain,(
    r2_hidden(sK5(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f318,f261])).

fof(f261,plain,(
    k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f170,f241])).

fof(f241,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f240,f33])).

fof(f240,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f237,f35])).

fof(f237,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2)),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f235,f167])).

fof(f167,plain,(
    v5_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f65,f157])).

fof(f157,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f156,f127])).

fof(f127,plain,
    ( r2_hidden(sK5(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f126,f73])).

fof(f73,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f32,f63])).

fof(f63,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f32,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f126,plain,
    ( r2_hidden(sK5(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | k1_xboole_0 = sK1
    | sK1 = k2_relat_1(sK2) ),
    inference(factoring,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,sK1),k2_relat_1(sK2))
      | k1_xboole_0 = sK1
      | r2_hidden(sK5(X0,sK1),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f85,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1
      | r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f84,f27])).

fof(f27,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK2))
      | ~ r2_hidden(sK3(X0),sK0)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f81,f28])).

fof(f28,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,sK3(X3)) = X3
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f79,f76])).

fof(f76,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f68,f62])).

fof(f62,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f67,f30])).

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f31,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f60,f61])).

fof(f61,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f156,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK5(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f153,f73])).

fof(f153,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK5(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f150,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f150,plain,
    ( r2_hidden(sK5(k2_relat_1(sK2),sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f128,f65])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | r2_hidden(sK5(k2_relat_1(sK2),sK1),X0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f127,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK2))
      | r2_hidden(X1,X0)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f70,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f70,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(sK2),X1)
      | ~ v5_relat_1(sK2,X1) ) ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f65,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f235,plain,(
    ! [X1] :
      ( ~ v5_relat_1(sK2,X1)
      | r2_hidden(sK4(k2_relat_1(sK2)),X1)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f233,f170])).

fof(f233,plain,(
    ! [X1] :
      ( k1_xboole_0 = k2_relat_1(sK2)
      | k1_xboole_0 = sK2
      | r2_hidden(sK4(k2_relat_1(sK2)),X1)
      | ~ v5_relat_1(sK2,X1) ) ),
    inference(resolution,[],[f229,f74])).

fof(f229,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f221,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f221,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = sK2
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f219,f35])).

fof(f219,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f218,f33])).

fof(f218,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,k1_xboole_0),X0)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f206,f182])).

fof(f182,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f174,f162])).

fof(f162,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f30,f157])).

fof(f174,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(resolution,[],[f163,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f163,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f31,f157])).

fof(f206,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f188,f35])).

fof(f188,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK5(X0,k1_xboole_0)),sK0)
      | r2_hidden(sK5(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f160,f39])).

fof(f160,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | r2_hidden(sK3(X3),sK0) ) ),
    inference(backward_demodulation,[],[f27,f157])).

fof(f170,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f73,f157])).

fof(f318,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(factoring,[],[f311])).

fof(f311,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),k1_xboole_0)
      | r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),X0)
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(forward_demodulation,[],[f310,f241])).

fof(f310,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),X0)
      | r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),k1_xboole_0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(forward_demodulation,[],[f309,f241])).

fof(f309,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),k1_xboole_0)
      | r2_hidden(sK5(X0,k2_relat_1(sK2)),X0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(forward_demodulation,[],[f308,f241])).

fof(f308,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k2_relat_1(sK2)),k1_xboole_0)
      | r2_hidden(sK5(X0,k2_relat_1(sK2)),X0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(forward_demodulation,[],[f131,f157])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,k2_relat_1(sK2)),sK1)
      | r2_hidden(sK5(X0,k2_relat_1(sK2)),X0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(resolution,[],[f78,f65])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK2,X1)
      | r2_hidden(sK5(X0,k2_relat_1(sK2)),X1)
      | r2_hidden(sK5(X0,k2_relat_1(sK2)),X0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(resolution,[],[f74,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:37:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (19020)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (19045)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (19023)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (19028)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (19028)Refutation not found, incomplete strategy% (19028)------------------------------
% 0.21/0.52  % (19028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19019)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (19039)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (19018)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (19041)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (19028)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19031)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (19028)Memory used [KB]: 10746
% 0.21/0.54  % (19028)Time elapsed: 0.110 s
% 0.21/0.54  % (19028)------------------------------
% 0.21/0.54  % (19028)------------------------------
% 0.21/0.54  % (19021)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (19033)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (19022)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (19022)Refutation not found, incomplete strategy% (19022)------------------------------
% 0.21/0.54  % (19022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19022)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19022)Memory used [KB]: 6268
% 0.21/0.54  % (19022)Time elapsed: 0.127 s
% 0.21/0.54  % (19022)------------------------------
% 0.21/0.54  % (19022)------------------------------
% 0.21/0.54  % (19042)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (19046)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (19047)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (19035)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (19029)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (19029)Refutation not found, incomplete strategy% (19029)------------------------------
% 0.21/0.55  % (19029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19029)Memory used [KB]: 10746
% 0.21/0.55  % (19029)Time elapsed: 0.141 s
% 0.21/0.55  % (19029)------------------------------
% 0.21/0.55  % (19029)------------------------------
% 0.21/0.55  % (19038)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (19027)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (19044)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (19030)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (19026)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (19036)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (19025)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (19034)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (19037)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (19044)Refutation not found, incomplete strategy% (19044)------------------------------
% 0.21/0.55  % (19044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19039)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (19043)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (19044)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19044)Memory used [KB]: 10746
% 0.21/0.56  % (19044)Time elapsed: 0.142 s
% 0.21/0.56  % (19044)------------------------------
% 0.21/0.56  % (19044)------------------------------
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f324,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f323,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.56  fof(f323,plain,(
% 0.21/0.56    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f320,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.56  fof(f320,plain,(
% 0.21/0.56    r2_hidden(sK5(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f318,f261])).
% 0.21/0.56  fof(f261,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(backward_demodulation,[],[f170,f241])).
% 0.21/0.56  fof(f241,plain,(
% 0.21/0.56    k1_xboole_0 = sK2),
% 0.21/0.56    inference(subsumption_resolution,[],[f240,f33])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f237,f35])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    r2_hidden(sK4(k2_relat_1(sK2)),k1_xboole_0) | k1_xboole_0 = sK2),
% 0.21/0.56    inference(resolution,[],[f235,f167])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    v5_relat_1(sK2,k1_xboole_0)),
% 0.21/0.56    inference(backward_demodulation,[],[f65,f157])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    k1_xboole_0 = sK1),
% 0.21/0.56    inference(subsumption_resolution,[],[f156,f127])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    r2_hidden(sK5(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | k1_xboole_0 = sK1),
% 0.21/0.56    inference(subsumption_resolution,[],[f126,f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    sK1 != k2_relat_1(sK2)),
% 0.21/0.56    inference(superposition,[],[f32,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f31,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f12])).
% 0.21/0.56  fof(f12,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    r2_hidden(sK5(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | k1_xboole_0 = sK1 | sK1 = k2_relat_1(sK2)),
% 0.21/0.56    inference(factoring,[],[f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(X0,sK1),k2_relat_1(sK2)) | k1_xboole_0 = sK1 | r2_hidden(sK5(X0,sK1),X0) | sK1 = X0) )),
% 0.21/0.56    inference(resolution,[],[f85,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK1 | r2_hidden(X0,k2_relat_1(sK2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f84,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | ~r2_hidden(sK3(X0),sK0) | k1_xboole_0 = sK1 | ~r2_hidden(X0,sK1)) )),
% 0.21/0.56    inference(superposition,[],[f81,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X3] : (k1_funct_1(sK2,sK3(X3)) = X3 | ~r2_hidden(X3,sK1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1) )),
% 0.21/0.56    inference(superposition,[],[f79,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.56    inference(superposition,[],[f68,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.56    inference(resolution,[],[f31,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.21/0.56    inference(subsumption_resolution,[],[f67,f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    inference(resolution,[],[f31,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f60,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    v1_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f31,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) )),
% 0.21/0.56    inference(resolution,[],[f29,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | ~r2_hidden(sK5(k2_relat_1(sK2),sK1),k2_relat_1(sK2))),
% 0.21/0.56    inference(subsumption_resolution,[],[f153,f73])).
% 0.21/0.56  fof(f153,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | ~r2_hidden(sK5(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f150,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    r2_hidden(sK5(k2_relat_1(sK2),sK1),sK1) | k1_xboole_0 = sK1),
% 0.21/0.56    inference(resolution,[],[f128,f65])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    ( ! [X0] : (~v5_relat_1(sK2,X0) | r2_hidden(sK5(k2_relat_1(sK2),sK1),X0) | k1_xboole_0 = sK1) )),
% 0.21/0.56    inference(resolution,[],[f127,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(sK2)) | r2_hidden(X1,X0) | ~v5_relat_1(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f70,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(k2_relat_1(sK2),X1) | ~v5_relat_1(sK2,X1)) )),
% 0.21/0.56    inference(resolution,[],[f61,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    v5_relat_1(sK2,sK1)),
% 0.21/0.56    inference(resolution,[],[f31,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.56  fof(f235,plain,(
% 0.21/0.56    ( ! [X1] : (~v5_relat_1(sK2,X1) | r2_hidden(sK4(k2_relat_1(sK2)),X1) | k1_xboole_0 = sK2) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f233,f170])).
% 0.21/0.56  fof(f233,plain,(
% 0.21/0.56    ( ! [X1] : (k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = sK2 | r2_hidden(sK4(k2_relat_1(sK2)),X1) | ~v5_relat_1(sK2,X1)) )),
% 0.21/0.56    inference(resolution,[],[f229,f74])).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2) )),
% 0.21/0.56    inference(resolution,[],[f221,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f221,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = sK2 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(resolution,[],[f219,f35])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(X0,k1_xboole_0),X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f218,f33])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = X0 | r2_hidden(sK5(X0,k1_xboole_0),X0) | k1_xboole_0 = sK2) )),
% 0.21/0.56    inference(superposition,[],[f206,f182])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 0.21/0.56    inference(subsumption_resolution,[],[f174,f162])).
% 0.21/0.56  fof(f162,plain,(
% 0.21/0.56    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.56    inference(backward_demodulation,[],[f30,f157])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f163,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.21/0.56    inference(backward_demodulation,[],[f31,f157])).
% 0.21/0.56  fof(f206,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(sK0) | k1_xboole_0 = X0 | r2_hidden(sK5(X0,k1_xboole_0),X0)) )),
% 0.21/0.56    inference(resolution,[],[f188,f35])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK3(sK5(X0,k1_xboole_0)),sK0) | r2_hidden(sK5(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(resolution,[],[f160,f39])).
% 0.21/0.56  fof(f160,plain,(
% 0.21/0.56    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | r2_hidden(sK3(X3),sK0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f27,f157])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    k1_xboole_0 != k2_relat_1(sK2)),
% 0.21/0.56    inference(backward_demodulation,[],[f73,f157])).
% 0.21/0.56  fof(f318,plain,(
% 0.21/0.56    r2_hidden(sK5(k1_xboole_0,k2_relat_1(k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(factoring,[],[f311])).
% 0.21/0.56  fof(f311,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),k1_xboole_0) | r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),X0) | k2_relat_1(k1_xboole_0) = X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f310,f241])).
% 0.21/0.56  fof(f310,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),X0) | r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),k1_xboole_0) | k2_relat_1(sK2) = X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f309,f241])).
% 0.21/0.56  fof(f309,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(X0,k2_relat_1(k1_xboole_0)),k1_xboole_0) | r2_hidden(sK5(X0,k2_relat_1(sK2)),X0) | k2_relat_1(sK2) = X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f308,f241])).
% 0.21/0.56  fof(f308,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(X0,k2_relat_1(sK2)),k1_xboole_0) | r2_hidden(sK5(X0,k2_relat_1(sK2)),X0) | k2_relat_1(sK2) = X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f131,f157])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK5(X0,k2_relat_1(sK2)),sK1) | r2_hidden(sK5(X0,k2_relat_1(sK2)),X0) | k2_relat_1(sK2) = X0) )),
% 0.21/0.56    inference(resolution,[],[f78,f65])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v5_relat_1(sK2,X1) | r2_hidden(sK5(X0,k2_relat_1(sK2)),X1) | r2_hidden(sK5(X0,k2_relat_1(sK2)),X0) | k2_relat_1(sK2) = X0) )),
% 0.21/0.56    inference(resolution,[],[f74,f39])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (19039)------------------------------
% 0.21/0.56  % (19039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19039)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (19039)Memory used [KB]: 1791
% 0.21/0.56  % (19039)Time elapsed: 0.157 s
% 0.21/0.56  % (19039)------------------------------
% 0.21/0.56  % (19039)------------------------------
% 0.21/0.56  % (19017)Success in time 0.196 s
%------------------------------------------------------------------------------

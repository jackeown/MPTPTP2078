%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 967 expanded)
%              Number of leaves         :   11 ( 223 expanded)
%              Depth                    :   26
%              Number of atoms          :  244 (3434 expanded)
%              Number of equality atoms :   64 ( 359 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f891,plain,(
    $false ),
    inference(resolution,[],[f886,f26])).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f886,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(global_subsumption,[],[f26,f501,f885])).

fof(f885,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f884,f27])).

fof(f27,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f884,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f859,f843])).

fof(f843,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f26,f842])).

fof(f842,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f741,f793])).

fof(f793,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(global_subsumption,[],[f26,f792])).

fof(f792,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f697,f680])).

fof(f680,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f230,f223,f234,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f234,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f223,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f223,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(unit_resulting_resolution,[],[f23,f25,f49,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f25,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f230,plain,(
    ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_subsumption,[],[f58,f223])).

fof(f58,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_subsumption,[],[f24,f22])).

fof(f22,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f697,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(backward_demodulation,[],[f110,f680])).

fof(f110,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f103,f74])).

fof(f74,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f79,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f79,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f48,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f741,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK1 = k2_relat_1(sK1) ),
    inference(backward_demodulation,[],[f274,f680])).

fof(f274,plain,
    ( sK1 = k2_relat_1(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK0)
    | sK1 = k2_relat_1(sK1) ),
    inference(resolution,[],[f260,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | ~ v1_xboole_0(sK0)
      | k2_relat_1(sK1) = X0 ) ),
    inference(resolution,[],[f83,f31])).

fof(f83,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK1),X0)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f80,f33])).

fof(f80,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_relat_1(sK1))
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f48,f63])).

fof(f63,plain,(
    m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f35])).

fof(f260,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f259,f33])).

fof(f259,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(sK0) ) ),
    inference(global_subsumption,[],[f26,f255])).

fof(f255,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f241,f48])).

fof(f241,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f240,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
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

fof(f240,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | ~ v1_xboole_0(sK0) ),
    inference(superposition,[],[f223,f141])).

fof(f141,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK0) ),
    inference(superposition,[],[f125,f110])).

fof(f125,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f87,f84])).

fof(f84,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f77,f33])).

fof(f77,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f26,f64,f48])).

fof(f859,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f821,f843])).

fof(f821,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),X0)
      | ~ v1_xboole_0(sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f26,f714])).

fof(f714,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),X0)
      | ~ v1_xboole_0(sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f192,f680])).

fof(f192,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK1,k1_relat_1(sK1),X0)
      | ~ v1_xboole_0(sK1)
      | ~ v1_xboole_0(sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f108,f182])).

fof(f182,plain,(
    ! [X3] :
      ( sK0 = X3
      | ~ v1_xboole_0(sK0)
      | ~ v1_xboole_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X3] :
      ( sK0 = X3
      | ~ v1_xboole_0(sK0)
      | ~ v1_xboole_0(X3)
      | ~ v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f124,f110])).

fof(f124,plain,(
    ! [X0] :
      ( k2_relat_1(sK1) = X0
      | ~ v1_xboole_0(sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f87,f103])).

fof(f108,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f103,f65])).

fof(f65,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f35,f58])).

fof(f501,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f95,f27,f154])).

fof(f154,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f151,f52])).

% (16044)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f151,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X3,k1_xboole_0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(superposition,[],[f60,f41])).

fof(f60,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f54,f52])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f84,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n001.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:23:59 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.48  % (16048)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.49  % (16057)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.52  % (16057)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 1.21/0.53  % SZS output start Proof for theBenchmark
% 1.21/0.53  fof(f891,plain,(
% 1.21/0.53    $false),
% 1.21/0.53    inference(resolution,[],[f886,f26])).
% 1.21/0.53  fof(f26,plain,(
% 1.21/0.53    v1_xboole_0(k1_xboole_0)),
% 1.21/0.53    inference(cnf_transformation,[],[f2])).
% 1.21/0.53  fof(f2,axiom,(
% 1.21/0.53    v1_xboole_0(k1_xboole_0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.21/0.53  fof(f886,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(global_subsumption,[],[f26,f501,f885])).
% 1.21/0.53  fof(f885,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(forward_demodulation,[],[f884,f27])).
% 1.21/0.53  fof(f27,plain,(
% 1.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.21/0.53    inference(cnf_transformation,[],[f7])).
% 1.21/0.53  fof(f7,axiom,(
% 1.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.21/0.53  fof(f884,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(forward_demodulation,[],[f859,f843])).
% 1.21/0.53  fof(f843,plain,(
% 1.21/0.53    k1_xboole_0 = sK1),
% 1.21/0.53    inference(global_subsumption,[],[f26,f842])).
% 1.21/0.53  fof(f842,plain,(
% 1.21/0.53    k1_xboole_0 = sK1 | ~v1_xboole_0(k1_xboole_0)),
% 1.21/0.53    inference(forward_demodulation,[],[f741,f793])).
% 1.21/0.53  fof(f793,plain,(
% 1.21/0.53    k1_xboole_0 = k2_relat_1(sK1)),
% 1.21/0.53    inference(global_subsumption,[],[f26,f792])).
% 1.21/0.53  fof(f792,plain,(
% 1.21/0.53    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK1)),
% 1.21/0.53    inference(forward_demodulation,[],[f697,f680])).
% 1.21/0.53  fof(f680,plain,(
% 1.21/0.53    k1_xboole_0 = sK0),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f230,f223,f234,f46])).
% 1.21/0.53  fof(f46,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f20,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(flattening,[],[f19])).
% 1.21/0.53  fof(f19,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(ennf_transformation,[],[f10])).
% 1.21/0.53  fof(f10,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.21/0.53  fof(f234,plain,(
% 1.21/0.53    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f223,f41])).
% 1.21/0.53  fof(f41,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f18])).
% 1.21/0.53  fof(f18,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(ennf_transformation,[],[f8])).
% 1.21/0.53  fof(f8,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.21/0.53  fof(f223,plain,(
% 1.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f23,f25,f49,f40])).
% 1.21/0.53  fof(f40,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f17])).
% 1.21/0.53  fof(f17,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.21/0.53    inference(flattening,[],[f16])).
% 1.21/0.53  fof(f16,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.21/0.53    inference(ennf_transformation,[],[f9])).
% 1.21/0.53  fof(f9,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.21/0.53  fof(f49,plain,(
% 1.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.21/0.53    inference(equality_resolution,[],[f30])).
% 1.21/0.53  fof(f30,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.21/0.53    inference(cnf_transformation,[],[f3])).
% 1.21/0.53  fof(f3,axiom,(
% 1.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.21/0.53  fof(f25,plain,(
% 1.21/0.53    r1_tarski(k2_relat_1(sK1),sK0)),
% 1.21/0.53    inference(cnf_transformation,[],[f14])).
% 1.21/0.53  fof(f14,plain,(
% 1.21/0.53    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.21/0.53    inference(flattening,[],[f13])).
% 1.21/0.53  fof(f13,plain,(
% 1.21/0.53    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.21/0.53    inference(ennf_transformation,[],[f12])).
% 1.21/0.53  fof(f12,negated_conjecture,(
% 1.21/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.21/0.53    inference(negated_conjecture,[],[f11])).
% 1.21/0.53  fof(f11,conjecture,(
% 1.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.21/0.53  fof(f23,plain,(
% 1.21/0.53    v1_relat_1(sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f14])).
% 1.21/0.53  fof(f230,plain,(
% 1.21/0.53    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 1.21/0.53    inference(global_subsumption,[],[f58,f223])).
% 1.21/0.53  fof(f58,plain,(
% 1.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 1.21/0.53    inference(global_subsumption,[],[f24,f22])).
% 1.21/0.53  fof(f22,plain,(
% 1.21/0.53    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 1.21/0.53    inference(cnf_transformation,[],[f14])).
% 1.21/0.53  fof(f24,plain,(
% 1.21/0.53    v1_funct_1(sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f14])).
% 1.21/0.53  fof(f697,plain,(
% 1.21/0.53    k1_xboole_0 = k2_relat_1(sK1) | ~v1_xboole_0(sK0)),
% 1.21/0.53    inference(backward_demodulation,[],[f110,f680])).
% 1.21/0.53  fof(f110,plain,(
% 1.21/0.53    sK0 = k2_relat_1(sK1) | ~v1_xboole_0(sK0)),
% 1.21/0.53    inference(resolution,[],[f103,f74])).
% 1.21/0.53  fof(f74,plain,(
% 1.21/0.53    ~r1_tarski(sK0,k2_relat_1(sK1)) | sK0 = k2_relat_1(sK1)),
% 1.21/0.53    inference(resolution,[],[f31,f25])).
% 1.21/0.53  fof(f31,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.21/0.53    inference(cnf_transformation,[],[f3])).
% 1.21/0.53  fof(f103,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(resolution,[],[f79,f33])).
% 1.21/0.53  fof(f33,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f15,plain,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.21/0.53    inference(ennf_transformation,[],[f1])).
% 1.21/0.53  fof(f1,axiom,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.21/0.53  fof(f79,plain,(
% 1.21/0.53    ( ! [X4,X3] : (~r2_hidden(X3,X4) | ~v1_xboole_0(X4)) )),
% 1.21/0.53    inference(resolution,[],[f48,f64])).
% 1.21/0.53  fof(f64,plain,(
% 1.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f49,f35])).
% 1.21/0.53  fof(f35,plain,(
% 1.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f5])).
% 1.21/0.53  fof(f5,axiom,(
% 1.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.21/0.53  fof(f48,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f21,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f6])).
% 1.21/0.53  fof(f6,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.21/0.53  fof(f741,plain,(
% 1.21/0.53    ~v1_xboole_0(k1_xboole_0) | sK1 = k2_relat_1(sK1)),
% 1.21/0.53    inference(backward_demodulation,[],[f274,f680])).
% 1.21/0.53  fof(f274,plain,(
% 1.21/0.53    sK1 = k2_relat_1(sK1) | ~v1_xboole_0(sK0)),
% 1.21/0.53    inference(duplicate_literal_removal,[],[f273])).
% 1.21/0.53  fof(f273,plain,(
% 1.21/0.53    ~v1_xboole_0(sK0) | ~v1_xboole_0(sK0) | sK1 = k2_relat_1(sK1)),
% 1.21/0.53    inference(resolution,[],[f260,f87])).
% 1.21/0.53  fof(f87,plain,(
% 1.21/0.53    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | ~v1_xboole_0(sK0) | k2_relat_1(sK1) = X0) )),
% 1.21/0.53    inference(resolution,[],[f83,f31])).
% 1.21/0.53  fof(f83,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(sK1),X0) | ~v1_xboole_0(sK0)) )),
% 1.21/0.53    inference(resolution,[],[f80,f33])).
% 1.21/0.53  fof(f80,plain,(
% 1.21/0.53    ( ! [X5] : (~r2_hidden(X5,k2_relat_1(sK1)) | ~v1_xboole_0(sK0)) )),
% 1.21/0.53    inference(resolution,[],[f48,f63])).
% 1.21/0.53  fof(f63,plain,(
% 1.21/0.53    m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f25,f35])).
% 1.21/0.53  fof(f260,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(sK1,X0) | ~v1_xboole_0(sK0)) )),
% 1.21/0.53    inference(resolution,[],[f259,f33])).
% 1.21/0.53  fof(f259,plain,(
% 1.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(sK0)) )),
% 1.21/0.53    inference(global_subsumption,[],[f26,f255])).
% 1.21/0.53  fof(f255,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_xboole_0(sK0) | ~r2_hidden(X0,sK1) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.21/0.53    inference(resolution,[],[f241,f48])).
% 1.21/0.53  fof(f241,plain,(
% 1.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(sK0)),
% 1.21/0.53    inference(forward_demodulation,[],[f240,f51])).
% 1.21/0.53  fof(f51,plain,(
% 1.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.21/0.53    inference(equality_resolution,[],[f39])).
% 1.21/0.53  fof(f39,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f4])).
% 1.21/0.53  fof(f4,axiom,(
% 1.21/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.21/0.53  fof(f240,plain,(
% 1.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) | ~v1_xboole_0(sK0)),
% 1.21/0.53    inference(superposition,[],[f223,f141])).
% 1.21/0.53  fof(f141,plain,(
% 1.21/0.53    k1_xboole_0 = sK0 | ~v1_xboole_0(sK0)),
% 1.21/0.53    inference(duplicate_literal_removal,[],[f129])).
% 1.21/0.53  fof(f129,plain,(
% 1.21/0.53    k1_xboole_0 = sK0 | ~v1_xboole_0(sK0) | ~v1_xboole_0(sK0)),
% 1.21/0.53    inference(superposition,[],[f125,f110])).
% 1.21/0.53  fof(f125,plain,(
% 1.21/0.53    k1_xboole_0 = k2_relat_1(sK1) | ~v1_xboole_0(sK0)),
% 1.21/0.53    inference(resolution,[],[f87,f84])).
% 1.21/0.53  fof(f84,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f77,f33])).
% 1.21/0.53  fof(f77,plain,(
% 1.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f26,f64,f48])).
% 1.21/0.53  fof(f859,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~v1_funct_2(sK1,k1_relat_1(sK1),X0) | ~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f821,f843])).
% 1.21/0.53  fof(f821,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_2(sK1,k1_relat_1(sK1),X0) | ~v1_xboole_0(sK1) | ~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(global_subsumption,[],[f26,f714])).
% 1.21/0.53  fof(f714,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~v1_funct_2(sK1,k1_relat_1(sK1),X0) | ~v1_xboole_0(sK1) | ~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(backward_demodulation,[],[f192,f680])).
% 1.21/0.53  fof(f192,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_2(sK1,k1_relat_1(sK1),X0) | ~v1_xboole_0(sK1) | ~v1_xboole_0(sK0) | ~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(superposition,[],[f108,f182])).
% 1.21/0.53  fof(f182,plain,(
% 1.21/0.53    ( ! [X3] : (sK0 = X3 | ~v1_xboole_0(sK0) | ~v1_xboole_0(X3)) )),
% 1.21/0.53    inference(duplicate_literal_removal,[],[f166])).
% 1.21/0.53  fof(f166,plain,(
% 1.21/0.53    ( ! [X3] : (sK0 = X3 | ~v1_xboole_0(sK0) | ~v1_xboole_0(X3) | ~v1_xboole_0(sK0)) )),
% 1.21/0.53    inference(superposition,[],[f124,f110])).
% 1.21/0.53  fof(f124,plain,(
% 1.21/0.53    ( ! [X0] : (k2_relat_1(sK1) = X0 | ~v1_xboole_0(sK0) | ~v1_xboole_0(X0)) )),
% 1.21/0.53    inference(resolution,[],[f87,f103])).
% 1.21/0.53  fof(f108,plain,(
% 1.21/0.53    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_xboole_0(sK1)),
% 1.21/0.53    inference(resolution,[],[f103,f65])).
% 1.21/0.53  fof(f65,plain,(
% 1.21/0.53    ~r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 1.21/0.53    inference(resolution,[],[f35,f58])).
% 1.21/0.53  fof(f501,plain,(
% 1.21/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f95,f27,f154])).
% 1.21/0.53  fof(f154,plain,(
% 1.21/0.53    ( ! [X2,X3] : (k1_xboole_0 != k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 1.21/0.53    inference(duplicate_literal_removal,[],[f153])).
% 1.21/0.53  fof(f153,plain,(
% 1.21/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 1.21/0.53    inference(forward_demodulation,[],[f151,f52])).
% 1.21/0.53  % (16044)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.53  fof(f52,plain,(
% 1.21/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.21/0.53    inference(equality_resolution,[],[f38])).
% 1.21/0.53  fof(f38,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f4])).
% 1.21/0.53  fof(f151,plain,(
% 1.21/0.53    ( ! [X2,X3] : (k1_xboole_0 != k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X3,k1_xboole_0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 1.21/0.53    inference(superposition,[],[f60,f41])).
% 1.21/0.53  fof(f60,plain,(
% 1.21/0.53    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.21/0.53    inference(forward_demodulation,[],[f54,f52])).
% 1.21/0.53  fof(f54,plain,(
% 1.21/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.21/0.53    inference(equality_resolution,[],[f44])).
% 1.21/0.53  fof(f44,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f95,plain,(
% 1.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.21/0.53    inference(unit_resulting_resolution,[],[f84,f35])).
% 1.21/0.53  % SZS output end Proof for theBenchmark
% 1.21/0.53  % (16057)------------------------------
% 1.21/0.53  % (16057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (16057)Termination reason: Refutation
% 1.21/0.53  
% 1.21/0.53  % (16057)Memory used [KB]: 6652
% 1.21/0.53  % (16057)Time elapsed: 0.081 s
% 1.21/0.53  % (16057)------------------------------
% 1.21/0.53  % (16057)------------------------------
% 1.21/0.53  % (16045)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.54  % (16032)Success in time 0.16 s
%------------------------------------------------------------------------------

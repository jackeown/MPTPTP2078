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
% DateTime   : Thu Dec  3 13:08:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 682 expanded)
%              Number of leaves         :   13 ( 136 expanded)
%              Depth                    :   28
%              Number of atoms          :  289 (3154 expanded)
%              Number of equality atoms :   73 ( 296 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(subsumption_resolution,[],[f515,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f515,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f92,f514])).

fof(f514,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f513,f495])).

fof(f495,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f494,f93])).

fof(f93,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f90,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f90,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f37,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f494,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f493,f92])).

fof(f493,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f487,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f487,plain,
    ( v5_relat_1(sK3,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f477,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f477,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f474])).

fof(f474,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f469,f123])).

fof(f123,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X1,sK3)),X1)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f122,f93])).

fof(f122,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X1,sK3)),X1)
      | ~ v1_relat_1(sK3)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f120,f35])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f120,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X1,sK3)),X1)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f71,f111])).

fof(f111,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f82,f87])).

fof(f87,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f37,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f80,f37])).

fof(f80,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f36,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f36,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f469,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f468,f92])).

fof(f468,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0)
    | k1_xboole_0 = sK2
    | r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0)
    | k1_xboole_0 = sK2
    | r1_tarski(k2_relat_1(sK3),sK0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f156,f446])).

fof(f446,plain,
    ( k1_funct_1(sK3,sK4(sK1,sK0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK4(sK1,sK0,sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f155,f92])).

fof(f155,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK3),X0)
      | k1_xboole_0 = sK2
      | k1_funct_1(sK3,sK4(sK1,X0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK4(sK1,X0,sK3)) ) ),
    inference(resolution,[],[f141,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f84,f37])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f40,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0,sK3),sK1)
      | r1_tarski(k2_relat_1(sK3),X0)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f137,f111])).

fof(f137,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
      | r1_tarski(k2_relat_1(sK3),X0) ) ),
    inference(resolution,[],[f134,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f134,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
      | r1_tarski(k2_relat_1(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f133,f93])).

fof(f133,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
      | r1_tarski(k2_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f126,f62])).

fof(f126,plain,(
    ! [X0] :
      ( v5_relat_1(sK3,X0)
      | r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f110,f66])).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
      | r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f78,f93])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) ) ),
    inference(resolution,[],[f35,f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK4(X0,X1,X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f156,plain,(
    ! [X1] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,sK4(sK1,X1,sK3)),sK0)
      | k1_xboole_0 = sK2
      | r1_tarski(k2_relat_1(sK3),X1) ) ),
    inference(resolution,[],[f141,f34])).

fof(f34,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f513,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f508,f65])).

fof(f508,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f100,f495])).

fof(f100,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(resolution,[],[f95,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f95,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f94,f93])).

fof(f94,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f86,f62])).

fof(f86,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f37,f66])).

fof(f92,plain,(
    ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f38,f89])).

fof(f89,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f38,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:45:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (22396)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (22401)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (22395)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (22393)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (22403)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (22407)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (22410)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (22411)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (22415)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (22402)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (22404)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (22409)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (22413)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (22405)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (22399)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (22398)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (22412)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (22397)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (22391)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (22392)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (22396)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f527,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f515,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f515,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f92,f514])).
% 0.21/0.54  fof(f514,plain,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(sK3)),
% 0.21/0.54    inference(forward_demodulation,[],[f513,f495])).
% 0.21/0.54  fof(f495,plain,(
% 0.21/0.54    k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f494,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f90,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f37,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f15])).
% 0.21/0.54  fof(f15,conjecture,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 0.21/0.54  fof(f494,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f493,f92])).
% 0.21/0.54  fof(f493,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f487,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.54  fof(f487,plain,(
% 0.21/0.54    v5_relat_1(sK3,sK0) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f477,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f477,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f474])).
% 0.21/0.54  fof(f474,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f469,f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X1,sK3)),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | k1_xboole_0 = sK2) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f122,f93])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X1,sK3)),X1) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | k1_xboole_0 = sK2) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f120,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    v1_funct_1(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X1,sK3)),X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | k1_xboole_0 = sK2) )),
% 0.21/0.54    inference(superposition,[],[f71,f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(superposition,[],[f82,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.54    inference(resolution,[],[f37,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f80,f37])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    inference(resolution,[],[f36,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.54  fof(f469,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f468,f92])).
% 0.21/0.54  fof(f468,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0) | k1_xboole_0 = sK2 | r1_tarski(k2_relat_1(sK3),sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f449])).
% 0.21/0.54  fof(f449,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0) | k1_xboole_0 = sK2 | r1_tarski(k2_relat_1(sK3),sK0) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(superposition,[],[f156,f446])).
% 0.21/0.54  fof(f446,plain,(
% 0.21/0.54    k1_funct_1(sK3,sK4(sK1,sK0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK4(sK1,sK0,sK3)) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f155,f92])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(sK3),X0) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK4(sK1,X0,sK3)) = k3_funct_2(sK1,sK2,sK3,sK4(sK1,X0,sK3))) )),
% 0.21/0.54    inference(resolution,[],[f141,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f84,f37])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f83,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f81,f35])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(sK3) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) )),
% 0.21/0.54    inference(resolution,[],[f36,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK4(sK1,X0,sK3),sK1) | r1_tarski(k2_relat_1(sK3),X0) | k1_xboole_0 = sK2) )),
% 0.21/0.54    inference(superposition,[],[f137,f111])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3)) | r1_tarski(k2_relat_1(sK3),X0)) )),
% 0.21/0.54    inference(resolution,[],[f134,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3)) | r1_tarski(k2_relat_1(sK3),X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f133,f93])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3)) | r1_tarski(k2_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 0.21/0.54    inference(resolution,[],[f126,f62])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X0] : (v5_relat_1(sK3,X0) | r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))) )),
% 0.21/0.54    inference(resolution,[],[f110,f66])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3))) )),
% 0.21/0.54    inference(resolution,[],[f78,f93])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(sK3) | r2_hidden(sK4(k1_relat_1(sK3),X0,sK3),k1_relat_1(sK3)) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) )),
% 0.21/0.54    inference(resolution,[],[f35,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK4(X0,X1,X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,sK4(sK1,X1,sK3)),sK0) | k1_xboole_0 = sK2 | r1_tarski(k2_relat_1(sK3),X1)) )),
% 0.21/0.54    inference(resolution,[],[f141,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X4] : (~m1_subset_1(X4,sK1) | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f513,plain,(
% 0.21/0.54    sK2 = k2_relat_1(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f508,f65])).
% 0.21/0.54  fof(f508,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 0.21/0.54    inference(backward_demodulation,[],[f100,f495])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ~r1_tarski(sK2,k2_relat_1(sK3)) | sK2 = k2_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f95,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f94,f93])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f86,f62])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    v5_relat_1(sK3,sK2)),
% 0.21/0.54    inference(resolution,[],[f37,f66])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(sK3),sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f38,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.54    inference(resolution,[],[f37,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (22396)------------------------------
% 0.21/0.54  % (22396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22396)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (22396)Memory used [KB]: 6396
% 0.21/0.54  % (22396)Time elapsed: 0.127 s
% 0.21/0.54  % (22396)------------------------------
% 0.21/0.54  % (22396)------------------------------
% 0.21/0.54  % (22388)Success in time 0.179 s
%------------------------------------------------------------------------------

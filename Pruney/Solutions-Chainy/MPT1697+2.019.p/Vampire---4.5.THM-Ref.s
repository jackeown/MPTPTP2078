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
% DateTime   : Thu Dec  3 13:17:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  182 (1419 expanded)
%              Number of leaves         :   16 ( 266 expanded)
%              Depth                    :   29
%              Number of atoms          :  884 (12106 expanded)
%              Number of equality atoms :  195 (2150 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f389,plain,(
    $false ),
    inference(subsumption_resolution,[],[f388,f384])).

fof(f384,plain,(
    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f383,f380])).

fof(f380,plain,(
    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f375,f379])).

fof(f379,plain,(
    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f377,f319])).

fof(f319,plain,(
    k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    inference(resolution,[],[f185,f108])).

fof(f108,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f107,f53])).

fof(f53,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f107,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f106,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f106,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f65,f52])).

fof(f52,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f185,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f183,f99])).

fof(f99,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f183,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v1_relat_1(sK5)
      | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    inference(superposition,[],[f60,f173])).

fof(f173,plain,(
    sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f172,f99])).

fof(f172,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f171,f101])).

fof(f101,plain,(
    v4_relat_1(sK5,sK3) ),
    inference(resolution,[],[f74,f46])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f171,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f120,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f120,plain,(
    v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f119,f45])).

fof(f45,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f119,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f44,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f118,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f116,f55])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f116,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3) ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f377,plain,(
    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
    inference(superposition,[],[f255,f178])).

fof(f178,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK2) ),
    inference(resolution,[],[f167,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f167,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f166,plain,
    ( r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3) ),
    inference(subsumption_resolution,[],[f164,f53])).

fof(f164,plain,
    ( v1_xboole_0(sK2)
    | r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f105,f65])).

fof(f105,plain,(
    r1_subset_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f104,f53])).

fof(f104,plain,
    ( v1_xboole_0(sK2)
    | r1_subset_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f103,f50])).

fof(f103,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | r1_subset_1(sK3,sK2) ),
    inference(resolution,[],[f63,f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | r1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(f255,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f114,f161])).

fof(f161,plain,(
    sK5 = k7_relat_1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f160,f99])).

fof(f160,plain,
    ( ~ v1_relat_1(sK5)
    | sK5 = k7_relat_1(sK5,sK3) ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f114,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK5,X0),X1) = k7_relat_1(sK5,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f71,f99])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f375,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f345,f373])).

fof(f373,plain,(
    k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    inference(resolution,[],[f214,f167])).

fof(f214,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f212,f100])).

fof(f100,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f212,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    inference(superposition,[],[f60,f176])).

fof(f176,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f175,f100])).

fof(f175,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f174,f102])).

fof(f102,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f74,f49])).

fof(f174,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f123,f68])).

fof(f123,plain,(
    v1_partfun1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f48,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f122,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f121,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f117,f55])).

fof(f117,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2) ),
    inference(resolution,[],[f62,f49])).

fof(f345,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,sK3)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f344,f169])).

fof(f169,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f108,f70])).

fof(f344,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f343,f126])).

fof(f126,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) ),
    inference(subsumption_resolution,[],[f124,f44])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK5)
      | k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) ) ),
    inference(resolution,[],[f75,f46])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f343,plain,
    ( k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f342,f256])).

fof(f256,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f115,f163])).

fof(f163,plain,(
    sK4 = k7_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f162,f100])).

fof(f162,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k7_relat_1(sK4,sK2) ),
    inference(resolution,[],[f102,f66])).

fof(f115,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK4,X0),X1) = k7_relat_1(sK4,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f100,f71])).

fof(f342,plain,
    ( k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f341,f109])).

fof(f109,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(resolution,[],[f72,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f341,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f340,f45])).

fof(f340,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f339,f44])).

fof(f339,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f338,f51])).

fof(f338,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f336,f50])).

fof(f336,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(resolution,[],[f230,f46])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X0))
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2) ) ),
    inference(forward_demodulation,[],[f229,f128])).

fof(f128,plain,(
    ! [X1] : k2_partfun1(sK2,sK1,sK4,X1) = k7_relat_1(sK4,X1) ),
    inference(subsumption_resolution,[],[f125,f47])).

fof(f125,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK4)
      | k2_partfun1(sK2,sK1,sK4,X1) = k7_relat_1(sK4,X1) ) ),
    inference(resolution,[],[f75,f49])).

fof(f229,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f228,f55])).

fof(f228,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f227,f48])).

fof(f227,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | v1_xboole_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f226,f47])).

fof(f226,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,sK2,sK1)
      | v1_xboole_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2) ) ),
    inference(resolution,[],[f153,f49])).

fof(f153,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK2,X4)
      | v1_xboole_0(X4)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X5,X4)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5))
      | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),sK2) = X6 ) ),
    inference(subsumption_resolution,[],[f149,f53])).

fof(f149,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_xboole_0(sK2)
      | v1_xboole_0(X4)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK2,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X5,X4)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5))
      | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),sK2) = X6 ) ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(subsumption_resolution,[],[f90,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(subsumption_resolution,[],[f76,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(subsumption_resolution,[],[f88,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(subsumption_resolution,[],[f77,f61])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(subsumption_resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(subsumption_resolution,[],[f82,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(subsumption_resolution,[],[f78,f61])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f383,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f382,f381])).

fof(f381,plain,(
    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f374,f379])).

fof(f374,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f371,f373])).

fof(f371,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,sK3)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f370,f169])).

fof(f370,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f369,f126])).

fof(f369,plain,
    ( k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f368,f256])).

fof(f368,plain,
    ( k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f367,f109])).

fof(f367,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f366,f45])).

fof(f366,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f365,f44])).

fof(f365,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f364,f51])).

fof(f364,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f362,f50])).

fof(f362,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(resolution,[],[f240,f46])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X0))
      | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1 ) ),
    inference(forward_demodulation,[],[f239,f128])).

fof(f239,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1 ) ),
    inference(subsumption_resolution,[],[f238,f55])).

fof(f238,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1 ) ),
    inference(subsumption_resolution,[],[f237,f48])).

fof(f237,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | v1_xboole_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1 ) ),
    inference(subsumption_resolution,[],[f236,f47])).

fof(f236,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,sK2,sK1)
      | v1_xboole_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1 ) ),
    inference(resolution,[],[f159,f49])).

fof(f159,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK2,X4)
      | v1_xboole_0(X4)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X5,X4)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5))
      | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),X5) = X7 ) ),
    inference(subsumption_resolution,[],[f155,f53])).

fof(f155,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_xboole_0(sK2)
      | v1_xboole_0(X4)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK2,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4)))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X5,X4)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5))
      | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),X5) = X7 ) ),
    inference(resolution,[],[f94,f54])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f91,f92])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f87,f89])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f86,f61])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f81,f84])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f382,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f170,f379])).

fof(f170,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f129,f169])).

fof(f129,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) ),
    inference(backward_demodulation,[],[f127,f128])).

fof(f127,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f113,f126])).

fof(f113,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f43,f109])).

fof(f43,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f388,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f386,f373])).

fof(f386,plain,(
    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(sK4,sK3) ),
    inference(superposition,[],[f256,f169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (7831)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (7827)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (7830)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (7824)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (7835)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (7838)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (7833)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (7826)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (7825)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (7836)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (7828)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (7841)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (7823)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (7842)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (7840)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (7839)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (7842)Refutation not found, incomplete strategy% (7842)------------------------------
% 0.20/0.51  % (7842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7842)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7842)Memory used [KB]: 10618
% 0.20/0.51  % (7842)Time elapsed: 0.093 s
% 0.20/0.51  % (7842)------------------------------
% 0.20/0.51  % (7842)------------------------------
% 0.20/0.51  % (7829)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (7822)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (7834)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (7832)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (7837)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.53  % (7823)Refutation not found, incomplete strategy% (7823)------------------------------
% 0.20/0.53  % (7823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7823)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7823)Memory used [KB]: 10746
% 0.20/0.53  % (7823)Time elapsed: 0.113 s
% 0.20/0.53  % (7823)------------------------------
% 0.20/0.53  % (7823)------------------------------
% 0.20/0.53  % (7839)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f389,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f388,f384])).
% 0.20/0.53  fof(f384,plain,(
% 0.20/0.53    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f383,f380])).
% 0.20/0.53  fof(f380,plain,(
% 0.20/0.53    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f375,f379])).
% 0.20/0.53  fof(f379,plain,(
% 0.20/0.53    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.20/0.53    inference(forward_demodulation,[],[f377,f319])).
% 0.20/0.53  fof(f319,plain,(
% 0.20/0.53    k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 0.20/0.53    inference(resolution,[],[f185,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    r1_xboole_0(sK2,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f107,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ~v1_xboole_0(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f16])).
% 0.20/0.53  fof(f16,conjecture,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f106,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ~v1_xboole_0(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 0.20/0.53    inference(resolution,[],[f65,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    r1_subset_1(sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f183,f99])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    v1_relat_1(sK5)),
% 0.20/0.53    inference(resolution,[],[f73,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) )),
% 0.20/0.53    inference(superposition,[],[f60,f173])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    sK3 = k1_relat_1(sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f172,f99])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f171,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    v4_relat_1(sK5,sK3)),
% 0.20/0.53    inference(resolution,[],[f74,f46])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5)),
% 0.20/0.53    inference(resolution,[],[f120,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    v1_partfun1(sK5,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f119,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    v1_funct_2(sK5,sK3,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f118,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    v1_funct_1(sK5)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f116,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3)),
% 0.20/0.53    inference(resolution,[],[f62,f46])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.53  fof(f377,plain,(
% 0.20/0.53    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2)),
% 0.20/0.53    inference(superposition,[],[f255,f178])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    k1_xboole_0 = k3_xboole_0(sK3,sK2)),
% 0.20/0.53    inference(resolution,[],[f167,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    r1_xboole_0(sK3,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f166,f50])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    r1_xboole_0(sK3,sK2) | v1_xboole_0(sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f164,f53])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    v1_xboole_0(sK2) | r1_xboole_0(sK3,sK2) | v1_xboole_0(sK3)),
% 0.20/0.53    inference(resolution,[],[f105,f65])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    r1_subset_1(sK3,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f104,f53])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    v1_xboole_0(sK2) | r1_subset_1(sK3,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f103,f50])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    v1_xboole_0(sK3) | v1_xboole_0(sK2) | r1_subset_1(sK3,sK2)),
% 0.20/0.53    inference(resolution,[],[f63,f52])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | r1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(sK3,X0))) )),
% 0.20/0.53    inference(superposition,[],[f114,f161])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    sK5 = k7_relat_1(sK5,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f160,f99])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    ~v1_relat_1(sK5) | sK5 = k7_relat_1(sK5,sK3)),
% 0.20/0.53    inference(resolution,[],[f101,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK5,X0),X1) = k7_relat_1(sK5,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(resolution,[],[f71,f99])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.53  fof(f375,plain,(
% 0.20/0.53    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(backward_demodulation,[],[f345,f373])).
% 0.20/0.53  fof(f373,plain,(
% 0.20/0.53    k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 0.20/0.53    inference(resolution,[],[f214,f167])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f212,f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    v1_relat_1(sK4)),
% 0.20/0.53    inference(resolution,[],[f73,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) )),
% 0.20/0.53    inference(superposition,[],[f60,f176])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    sK2 = k1_relat_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f175,f100])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f174,f102])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    v4_relat_1(sK4,sK2)),
% 0.20/0.53    inference(resolution,[],[f74,f49])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.53    inference(resolution,[],[f123,f68])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    v1_partfun1(sK4,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f122,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    v1_funct_2(sK4,sK2,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f121,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    v1_funct_1(sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f117,f55])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2)),
% 0.20/0.53    inference(resolution,[],[f62,f49])).
% 0.20/0.53  fof(f345,plain,(
% 0.20/0.53    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,sK3) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(forward_demodulation,[],[f344,f169])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.20/0.53    inference(resolution,[],[f108,f70])).
% 0.20/0.53  fof(f344,plain,(
% 0.20/0.53    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(forward_demodulation,[],[f343,f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f124,f44])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) )),
% 0.20/0.53    inference(resolution,[],[f75,f46])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.53  fof(f343,plain,(
% 0.20/0.53    k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(forward_demodulation,[],[f342,f256])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0))) )),
% 0.20/0.53    inference(superposition,[],[f115,f163])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    sK4 = k7_relat_1(sK4,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f162,f100])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    ~v1_relat_1(sK4) | sK4 = k7_relat_1(sK4,sK2)),
% 0.20/0.53    inference(resolution,[],[f102,f66])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK4,X0),X1) = k7_relat_1(sK4,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(resolution,[],[f100,f71])).
% 0.20/0.53  fof(f342,plain,(
% 0.20/0.53    k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(forward_demodulation,[],[f341,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)) )),
% 0.20/0.53    inference(resolution,[],[f72,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f340,f45])).
% 0.20/0.53  fof(f340,plain,(
% 0.20/0.53    ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f339,f44])).
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f338,f51])).
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f336,f50])).
% 0.20/0.53  fof(f336,plain,(
% 0.20/0.53    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(resolution,[],[f230,f46])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f229,f128])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,X1) = k7_relat_1(sK4,X1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f125,f47])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_funct_1(sK4) | k2_partfun1(sK2,sK1,sK4,X1) = k7_relat_1(sK4,X1)) )),
% 0.20/0.53    inference(resolution,[],[f75,f49])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f228,f55])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f227,f48])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f226,f47])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 0.20/0.53    inference(resolution,[],[f153,f49])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | v1_xboole_0(X4) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),sK2) = X6) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f149,f53])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    ( ! [X6,X4,X7,X5] : (v1_xboole_0(sK2) | v1_xboole_0(X4) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),sK2) = X6) )),
% 0.20/0.53    inference(resolution,[],[f93,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f90,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f76,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f88,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f77,f61])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f85,f61])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f82,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f78,f61])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.20/0.53    inference(equality_resolution,[],[f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.20/0.53  fof(f383,plain,(
% 0.20/0.53    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f382,f381])).
% 0.20/0.53  fof(f381,plain,(
% 0.20/0.53    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f374,f379])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.53    inference(backward_demodulation,[],[f371,f373])).
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,sK3) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.53    inference(forward_demodulation,[],[f370,f169])).
% 0.20/0.53  fof(f370,plain,(
% 0.20/0.53    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.53    inference(forward_demodulation,[],[f369,f126])).
% 0.20/0.54  fof(f369,plain,(
% 0.20/0.54    k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(forward_demodulation,[],[f368,f256])).
% 0.20/0.54  fof(f368,plain,(
% 0.20/0.54    k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(forward_demodulation,[],[f367,f109])).
% 0.20/0.54  fof(f367,plain,(
% 0.20/0.54    k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(subsumption_resolution,[],[f366,f45])).
% 0.20/0.54  fof(f366,plain,(
% 0.20/0.54    ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(subsumption_resolution,[],[f365,f44])).
% 0.20/0.54  fof(f365,plain,(
% 0.20/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(subsumption_resolution,[],[f364,f51])).
% 0.20/0.54  fof(f364,plain,(
% 0.20/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(subsumption_resolution,[],[f362,f50])).
% 0.20/0.54  fof(f362,plain,(
% 0.20/0.54    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(resolution,[],[f240,f46])).
% 0.20/0.54  fof(f240,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 0.20/0.54    inference(forward_demodulation,[],[f239,f128])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f238,f55])).
% 0.20/0.54  fof(f238,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f237,f48])).
% 0.20/0.54  fof(f237,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f236,f47])).
% 0.20/0.54  fof(f236,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 0.20/0.54    inference(resolution,[],[f159,f49])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | v1_xboole_0(X4) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),X5) = X7) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f155,f53])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X6,X4,X7,X5] : (v1_xboole_0(sK2) | v1_xboole_0(X4) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),X5) = X7) )),
% 0.20/0.54    inference(resolution,[],[f94,f54])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f91,f92])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f87,f89])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f86,f61])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f81,f84])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.20/0.54    inference(equality_resolution,[],[f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f382,plain,(
% 0.20/0.54    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f170,f379])).
% 0.20/0.54  fof(f170,plain,(
% 0.20/0.54    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f129,f169])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))),
% 0.20/0.54    inference(backward_demodulation,[],[f127,f128])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(backward_demodulation,[],[f113,f126])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(backward_demodulation,[],[f43,f109])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f388,plain,(
% 0.20/0.54    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.20/0.54    inference(forward_demodulation,[],[f386,f373])).
% 0.20/0.54  fof(f386,plain,(
% 0.20/0.54    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(sK4,sK3)),
% 0.20/0.54    inference(superposition,[],[f256,f169])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (7839)------------------------------
% 0.20/0.54  % (7839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7839)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (7839)Memory used [KB]: 2046
% 0.20/0.54  % (7839)Time elapsed: 0.131 s
% 0.20/0.54  % (7839)------------------------------
% 0.20/0.54  % (7839)------------------------------
% 0.20/0.54  % (7821)Success in time 0.181 s
%------------------------------------------------------------------------------

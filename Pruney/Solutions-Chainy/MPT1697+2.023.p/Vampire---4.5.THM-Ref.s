%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 (1280 expanded)
%              Number of leaves         :   16 ( 248 expanded)
%              Depth                    :   28
%              Number of atoms          :  925 (10817 expanded)
%              Number of equality atoms :  187 (1965 expanded)
%              Maximal formula depth    :   34 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f457,plain,(
    $false ),
    inference(global_subsumption,[],[f160,f363,f456])).

fof(f456,plain,(
    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f455,f47])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
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

fof(f455,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f454,f46])).

fof(f46,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f454,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f453,f45])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f453,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f452,f126])).

fof(f126,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f123,f105])).

fof(f105,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3) ),
    inference(resolution,[],[f103,f90])).

fof(f90,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f71,f47])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK2),sK3) ) ),
    inference(resolution,[],[f69,f97])).

fof(f97,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f96,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f93,f48])).

fof(f48,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f123,plain,(
    k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[],[f115,f98])).

fof(f98,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f97,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f67,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

% (13248)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f115,plain,(
    ! [X2,X3] : k7_relat_1(k7_relat_1(sK4,X2),X3) = k7_relat_1(sK4,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(resolution,[],[f79,f90])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f68,f60])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f452,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(superposition,[],[f451,f158])).

fof(f158,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    inference(resolution,[],[f137,f47])).

fof(f137,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k2_partfun1(X3,X4,sK4,X5) = k7_relat_1(sK4,X5) ) ),
    inference(resolution,[],[f73,f45])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f451,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(forward_demodulation,[],[f450,f145])).

fof(f145,plain,(
    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f104,f144])).

fof(f144,plain,(
    k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    inference(resolution,[],[f143,f97])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f141,f89])).

fof(f89,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f71,f44])).

fof(f44,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v1_relat_1(sK5)
      | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    inference(superposition,[],[f58,f140])).

fof(f140,plain,(
    sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f139,f89])).

fof(f139,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f138,f91])).

fof(f91,plain,(
    v4_relat_1(sK5,sK3) ),
    inference(resolution,[],[f72,f44])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f138,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f135,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f135,plain,(
    v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f134,f43])).

fof(f43,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f134,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f133,f53])).

fof(f53,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f133,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3) ),
    inference(resolution,[],[f131,f44])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(sK5,X0,X1)
      | v1_partfun1(sK5,X0) ) ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
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

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f104,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,sK2),sK3) ),
    inference(resolution,[],[f103,f89])).

fof(f450,plain,(
    ! [X1] :
      ( k7_relat_1(k1_xboole_0,sK3) != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(forward_demodulation,[],[f449,f144])).

fof(f449,plain,(
    ! [X1] :
      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(forward_demodulation,[],[f448,f110])).

fof(f110,plain,(
    k1_xboole_0 = k9_subset_1(sK0,sK2,sK3) ),
    inference(superposition,[],[f106,f98])).

fof(f106,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(resolution,[],[f80,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f70,f60])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f448,plain,(
    ! [X1] :
      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f446,f51])).

fof(f446,plain,(
    ! [X1] :
      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_xboole_0(sK2)
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(resolution,[],[f444,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f444,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k7_relat_1(k7_relat_1(sK5,X0),sK3) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1 ) ),
    inference(forward_demodulation,[],[f443,f120])).

fof(f120,plain,(
    ! [X0] : k7_relat_1(k7_relat_1(sK5,X0),sK3) = k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) ),
    inference(superposition,[],[f114,f106])).

fof(f114,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK5,X0),X1) = k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(resolution,[],[f79,f89])).

fof(f443,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1 ) ),
    inference(resolution,[],[f442,f49])).

fof(f442,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X1,X0,sK3))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2 ) ),
    inference(forward_demodulation,[],[f441,f155])).

fof(f155,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) ),
    inference(resolution,[],[f136,f44])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ) ),
    inference(resolution,[],[f73,f42])).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2 ) ),
    inference(subsumption_resolution,[],[f440,f43])).

fof(f440,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ v1_funct_2(sK5,sK3,sK1)
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2 ) ),
    inference(subsumption_resolution,[],[f439,f53])).

fof(f439,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(sK1)
      | ~ v1_funct_2(sK5,sK3,sK1)
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2 ) ),
    inference(subsumption_resolution,[],[f438,f48])).

fof(f438,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(sK1)
      | ~ v1_funct_2(sK5,sK3,sK1)
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2 ) ),
    inference(resolution,[],[f430,f44])).

fof(f430,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X4)))
      | v1_xboole_0(X4)
      | ~ v1_funct_2(sK5,X2,X4)
      | v1_xboole_0(X0)
      | k2_partfun1(X0,X4,X3,k9_subset_1(X1,X0,X2)) != k2_partfun1(X2,X4,sK5,k9_subset_1(X1,X0,X2))
      | k2_partfun1(k4_subset_1(X1,X0,X2),X4,k1_tmap_1(X1,X4,X0,X2,X3,sK5),X0) = X3 ) ),
    inference(resolution,[],[f240,f42])).

fof(f240,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4 ) ),
    inference(subsumption_resolution,[],[f239,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | v1_xboole_0(X1)
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(subsumption_resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
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

% (13247)Refutation not found, incomplete strategy% (13247)------------------------------
% (13247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13247)Termination reason: Refutation not found, incomplete strategy

% (13247)Memory used [KB]: 10746
% (13247)Time elapsed: 0.152 s
% (13247)------------------------------
% (13247)------------------------------
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
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f239,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4 ) ),
    inference(subsumption_resolution,[],[f238,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f75,f59])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f238,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | ~ v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0)
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4 ) ),
    inference(subsumption_resolution,[],[f237,f59])).

fof(f237,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | v1_xboole_0(X2)
      | ~ v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0)
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4 ) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | v1_xboole_0(X2)
      | ~ v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0)
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f84,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
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
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f74,f59])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
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
      | v1_xboole_0(X0)
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
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

fof(f363,plain,(
    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f362,f47])).

fof(f362,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f361,f46])).

fof(f361,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f360,f45])).

fof(f360,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f359,f126])).

fof(f359,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(superposition,[],[f358,f158])).

fof(f358,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(forward_demodulation,[],[f357,f145])).

fof(f357,plain,(
    ! [X1] :
      ( k7_relat_1(k1_xboole_0,sK3) != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(forward_demodulation,[],[f356,f144])).

fof(f356,plain,(
    ! [X1] :
      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(forward_demodulation,[],[f355,f110])).

fof(f355,plain,(
    ! [X1] :
      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(subsumption_resolution,[],[f353,f51])).

fof(f353,plain,(
    ! [X1] :
      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_xboole_0(sK2)
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(resolution,[],[f351,f52])).

fof(f351,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k7_relat_1(k7_relat_1(sK5,X0),sK3) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) ) ),
    inference(forward_demodulation,[],[f350,f120])).

fof(f350,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) ) ),
    inference(resolution,[],[f349,f49])).

fof(f349,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X1,X0,sK3))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3) ) ),
    inference(forward_demodulation,[],[f348,f155])).

fof(f348,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3) ) ),
    inference(subsumption_resolution,[],[f347,f43])).

fof(f347,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ v1_funct_2(sK5,sK3,sK1)
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3) ) ),
    inference(subsumption_resolution,[],[f346,f53])).

fof(f346,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(sK1)
      | ~ v1_funct_2(sK5,sK3,sK1)
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3) ) ),
    inference(subsumption_resolution,[],[f345,f48])).

fof(f345,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(sK1)
      | ~ v1_funct_2(sK5,sK3,sK1)
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3) ) ),
    inference(resolution,[],[f342,f44])).

fof(f342,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X4)))
      | v1_xboole_0(X4)
      | ~ v1_funct_2(sK5,X2,X4)
      | v1_xboole_0(X0)
      | k2_partfun1(X0,X4,X3,k9_subset_1(X1,X0,X2)) != k2_partfun1(X2,X4,sK5,k9_subset_1(X1,X0,X2))
      | sK5 = k2_partfun1(k4_subset_1(X1,X0,X2),X4,k1_tmap_1(X1,X4,X0,X2,X3,sK5),X2) ) ),
    inference(resolution,[],[f208,f42])).

fof(f208,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f207,f86])).

fof(f207,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f206,f87])).

fof(f206,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | ~ v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0)
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f205,f59])).

fof(f205,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | v1_xboole_0(X2)
      | ~ v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0)
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5 ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3))
      | v1_xboole_0(X2)
      | ~ v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0)
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f83,f88])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
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
      | v1_xboole_0(X0)
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
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

% (13239)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f160,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f159,f126])).

fof(f159,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f157,f158])).

fof(f157,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f156,f122])).

fof(f122,plain,(
    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f119,f104])).

fof(f119,plain,(
    k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[],[f114,f98])).

fof(f156,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f113,f155])).

fof(f113,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f41,f110])).

fof(f41,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:51:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.44  % (13235)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.47  % (13258)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.48  % (13250)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.48  % (13243)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.49  % (13236)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (13259)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.50  % (13234)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (13232)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (13251)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (13231)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (13233)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (13242)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (13253)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (13254)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (13257)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (13230)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (13246)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (13255)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (13237)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (13249)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (13236)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (13245)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (13247)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (13241)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (13240)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (13256)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f457,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(global_subsumption,[],[f160,f363,f456])).
% 0.20/0.55  fof(f456,plain,(
% 0.20/0.55    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f455,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.55    inference(flattening,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,negated_conjecture,(
% 0.20/0.55    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.20/0.55    inference(negated_conjecture,[],[f16])).
% 0.20/0.55  fof(f16,conjecture,(
% 0.20/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.20/0.55  fof(f455,plain,(
% 0.20/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f454,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    v1_funct_2(sK4,sK2,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f454,plain,(
% 0.20/0.55    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f453,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    v1_funct_1(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f453,plain,(
% 0.20/0.55    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f452,f126])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.20/0.55    inference(forward_demodulation,[],[f123,f105])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3)),
% 0.20/0.55    inference(resolution,[],[f103,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    v1_relat_1(sK4)),
% 0.20/0.55    inference(resolution,[],[f71,f47])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK2),sK3)) )),
% 0.20/0.55    inference(resolution,[],[f69,f97])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    r1_xboole_0(sK2,sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f96,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ~v1_xboole_0(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f93,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ~v1_xboole_0(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 0.20/0.55    inference(resolution,[],[f63,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    r1_subset_1(sK2,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.55    inference(flattening,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~v1_relat_1(X2) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(flattening,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k7_relat_1(sK4,k1_xboole_0)),
% 0.20/0.55    inference(superposition,[],[f115,f98])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 0.20/0.55    inference(resolution,[],[f97,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f67,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.55  % (13248)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK4,X2),X3) = k7_relat_1(sK4,k1_setfam_1(k2_tarski(X2,X3)))) )),
% 0.20/0.55    inference(resolution,[],[f79,f90])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f68,f60])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.55  fof(f452,plain,(
% 0.20/0.55    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.55    inference(superposition,[],[f451,f158])).
% 0.20/0.55  fof(f158,plain,(
% 0.20/0.55    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) )),
% 0.20/0.55    inference(resolution,[],[f137,f47])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_partfun1(X3,X4,sK4,X5) = k7_relat_1(sK4,X5)) )),
% 0.20/0.55    inference(resolution,[],[f73,f45])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.55  fof(f451,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 0.20/0.55    inference(forward_demodulation,[],[f450,f145])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3)),
% 0.20/0.55    inference(backward_demodulation,[],[f104,f144])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 0.20/0.55    inference(resolution,[],[f143,f97])).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f141,f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    v1_relat_1(sK5)),
% 0.20/0.55    inference(resolution,[],[f71,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) )),
% 0.20/0.55    inference(superposition,[],[f58,f140])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    sK3 = k1_relat_1(sK5)),
% 0.20/0.55    inference(subsumption_resolution,[],[f139,f89])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5)),
% 0.20/0.55    inference(subsumption_resolution,[],[f138,f91])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    v4_relat_1(sK5,sK3)),
% 0.20/0.55    inference(resolution,[],[f72,f44])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5)),
% 0.20/0.55    inference(resolution,[],[f135,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    v1_partfun1(sK5,sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f134,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    v1_funct_2(sK5,sK3,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f133,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ~v1_xboole_0(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3)),
% 0.20/0.55    inference(resolution,[],[f131,f44])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK5,X0,X1) | v1_partfun1(sK5,X0)) )),
% 0.20/0.55    inference(resolution,[],[f61,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    v1_funct_1(sK5)),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.55    inference(flattening,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,sK2),sK3)),
% 0.20/0.55    inference(resolution,[],[f103,f89])).
% 0.20/0.55  fof(f450,plain,(
% 0.20/0.55    ( ! [X1] : (k7_relat_1(k1_xboole_0,sK3) != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 0.20/0.55    inference(forward_demodulation,[],[f449,f144])).
% 0.20/0.55  fof(f449,plain,(
% 0.20/0.55    ( ! [X1] : (k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 0.20/0.55    inference(forward_demodulation,[],[f448,f110])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    k1_xboole_0 = k9_subset_1(sK0,sK2,sK3)),
% 0.20/0.55    inference(superposition,[],[f106,f98])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3))) )),
% 0.20/0.55    inference(resolution,[],[f80,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f70,f60])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.55  fof(f448,plain,(
% 0.20/0.55    ( ! [X1] : (k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f446,f51])).
% 0.20/0.55  fof(f446,plain,(
% 0.20/0.55    ( ! [X1] : (k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | v1_xboole_0(sK2) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 0.20/0.55    inference(resolution,[],[f444,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f444,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k7_relat_1(k7_relat_1(sK5,X0),sK3) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1) )),
% 0.20/0.55    inference(forward_demodulation,[],[f443,f120])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    ( ! [X0] : (k7_relat_1(k7_relat_1(sK5,X0),sK3) = k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3))) )),
% 0.20/0.55    inference(superposition,[],[f114,f106])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK5,X0),X1) = k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.55    inference(resolution,[],[f79,f89])).
% 0.20/0.55  fof(f443,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1) )),
% 0.20/0.55    inference(resolution,[],[f442,f49])).
% 0.20/0.55  fof(f442,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X1,X0,sK3)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 0.20/0.55    inference(forward_demodulation,[],[f441,f155])).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) )),
% 0.20/0.55    inference(resolution,[],[f136,f44])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2)) )),
% 0.20/0.55    inference(resolution,[],[f73,f42])).
% 0.20/0.55  fof(f441,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f440,f43])).
% 0.20/0.55  fof(f440,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f439,f53])).
% 0.20/0.55  fof(f439,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f438,f48])).
% 0.20/0.55  fof(f438,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 0.20/0.55    inference(resolution,[],[f430,f44])).
% 0.20/0.55  fof(f430,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X4))) | v1_xboole_0(X4) | ~v1_funct_2(sK5,X2,X4) | v1_xboole_0(X0) | k2_partfun1(X0,X4,X3,k9_subset_1(X1,X0,X2)) != k2_partfun1(X2,X4,sK5,k9_subset_1(X1,X0,X2)) | k2_partfun1(k4_subset_1(X1,X0,X2),X4,k1_tmap_1(X1,X4,X0,X2,X3,sK5),X0) = X3) )),
% 0.20/0.55    inference(resolution,[],[f240,f42])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X0) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f239,f86])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | v1_xboole_0(X1) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f76,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.55  % (13247)Refutation not found, incomplete strategy% (13247)------------------------------
% 0.20/0.55  % (13247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13247)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (13247)Memory used [KB]: 10746
% 0.20/0.55  % (13247)Time elapsed: 0.152 s
% 0.20/0.55  % (13247)------------------------------
% 0.20/0.55  % (13247)------------------------------
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.55    inference(flattening,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.20/0.55  fof(f239,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f238,f87])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f75,f59])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f237,f59])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | v1_xboole_0(X2) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f236])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | v1_xboole_0(X2) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4 | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(resolution,[],[f84,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f74,f59])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.20/0.55    inference(equality_resolution,[],[f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.55    inference(flattening,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.20/0.55  fof(f363,plain,(
% 0.20/0.55    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f362,f47])).
% 0.20/0.55  fof(f362,plain,(
% 0.20/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f361,f46])).
% 0.20/0.55  fof(f361,plain,(
% 0.20/0.55    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f360,f45])).
% 0.20/0.55  fof(f360,plain,(
% 0.20/0.55    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f359,f126])).
% 0.20/0.55  fof(f359,plain,(
% 0.20/0.55    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.55    inference(superposition,[],[f358,f158])).
% 0.20/0.55  fof(f358,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f357,f145])).
% 0.20/0.55  fof(f357,plain,(
% 0.20/0.55    ( ! [X1] : (k7_relat_1(k1_xboole_0,sK3) != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f356,f144])).
% 0.20/0.55  fof(f356,plain,(
% 0.20/0.55    ( ! [X1] : (k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f355,f110])).
% 0.20/0.55  fof(f355,plain,(
% 0.20/0.55    ( ! [X1] : (k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f353,f51])).
% 0.20/0.55  fof(f353,plain,(
% 0.20/0.55    ( ! [X1] : (k7_relat_1(k7_relat_1(sK5,sK2),sK3) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | v1_xboole_0(sK2) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 0.20/0.55    inference(resolution,[],[f351,f52])).
% 0.20/0.55  fof(f351,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k7_relat_1(k7_relat_1(sK5,X0),sK3) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f350,f120])).
% 0.20/0.55  fof(f350,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)) )),
% 0.20/0.55    inference(resolution,[],[f349,f49])).
% 0.20/0.55  fof(f349,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X1,X0,sK3)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f348,f155])).
% 0.20/0.55  fof(f348,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f347,f43])).
% 0.20/0.55  fof(f347,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f346,f53])).
% 0.20/0.55  fof(f346,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f345,f48])).
% 0.20/0.55  fof(f345,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 0.20/0.55    inference(resolution,[],[f342,f44])).
% 0.20/0.55  fof(f342,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X4))) | v1_xboole_0(X4) | ~v1_funct_2(sK5,X2,X4) | v1_xboole_0(X0) | k2_partfun1(X0,X4,X3,k9_subset_1(X1,X0,X2)) != k2_partfun1(X2,X4,sK5,k9_subset_1(X1,X0,X2)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,X2),X4,k1_tmap_1(X1,X4,X0,X2,X3,sK5),X2)) )),
% 0.20/0.55    inference(resolution,[],[f208,f42])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X0) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f207,f86])).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f206,f87])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f205,f59])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | v1_xboole_0(X2) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f204])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | v1_xboole_0(X2) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5 | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(resolution,[],[f83,f88])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.20/0.55    inference(equality_resolution,[],[f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  % (13239)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  fof(f160,plain,(
% 0.20/0.56    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.56    inference(subsumption_resolution,[],[f159,f126])).
% 0.20/0.56  fof(f159,plain,(
% 0.20/0.56    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f157,f158])).
% 0.20/0.56  fof(f157,plain,(
% 0.20/0.56    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.56    inference(forward_demodulation,[],[f156,f122])).
% 0.20/0.56  fof(f122,plain,(
% 0.20/0.56    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.20/0.56    inference(forward_demodulation,[],[f119,f104])).
% 0.20/0.56  fof(f119,plain,(
% 0.20/0.56    k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k7_relat_1(sK5,k1_xboole_0)),
% 0.20/0.56    inference(superposition,[],[f114,f98])).
% 0.20/0.56  fof(f156,plain,(
% 0.20/0.56    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f113,f155])).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.56    inference(backward_demodulation,[],[f41,f110])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (13236)------------------------------
% 0.20/0.56  % (13236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (13236)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (13236)Memory used [KB]: 7036
% 0.20/0.56  % (13236)Time elapsed: 0.141 s
% 0.20/0.56  % (13236)------------------------------
% 0.20/0.56  % (13236)------------------------------
% 1.61/0.57  % (13227)Success in time 0.218 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  168 (1111 expanded)
%              Number of leaves         :   15 ( 211 expanded)
%              Depth                    :   28
%              Number of atoms          :  815 (9353 expanded)
%              Number of equality atoms :  186 (1721 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f589,plain,(
    $false ),
    inference(subsumption_resolution,[],[f588,f577])).

fof(f577,plain,(
    k1_xboole_0 != k7_relat_1(sK4,sK3) ),
    inference(backward_demodulation,[],[f530,f576])).

fof(f576,plain,(
    k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    inference(resolution,[],[f235,f125])).

fof(f125,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f124,f56])).

fof(f56,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f124,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f123,f53])).

fof(f53,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f123,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f235,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f233,f111])).

fof(f111,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f233,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK3)
      | ~ v1_relat_1(sK5)
      | k1_xboole_0 = k7_relat_1(sK5,X0) ) ),
    inference(superposition,[],[f67,f197])).

fof(f197,plain,(
    sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f196,f111])).

fof(f196,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f195,f115])).

fof(f115,plain,(
    v4_relat_1(sK5,sK3) ),
    inference(resolution,[],[f83,f49])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f195,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f141,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f141,plain,(
    v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f140,f48])).

fof(f48,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f140,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f139,f47])).

fof(f47,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f139,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f137,f58])).

fof(f58,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3) ),
    inference(resolution,[],[f74,f49])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f530,plain,(
    k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f529,f504])).

fof(f504,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) ),
    inference(subsumption_resolution,[],[f353,f503])).

fof(f503,plain,
    ( k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f502,f350])).

fof(f350,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f199,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f199,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(sK3,X0)) ),
    inference(backward_demodulation,[],[f131,f198])).

fof(f198,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(sK3,X0) ),
    inference(backward_demodulation,[],[f129,f197])).

fof(f129,plain,(
    ! [X0] : k3_xboole_0(k1_relat_1(sK5),X0) = k1_relat_1(k7_relat_1(sK5,X0)) ),
    inference(resolution,[],[f75,f111])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f131,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0))) ),
    inference(forward_demodulation,[],[f130,f129])).

fof(f130,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0)) ),
    inference(resolution,[],[f76,f111])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f502,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f501,f147])).

fof(f147,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) ),
    inference(subsumption_resolution,[],[f145,f47])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK5)
      | k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) ) ),
    inference(resolution,[],[f84,f49])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f501,plain,
    ( k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f500,f204])).

fof(f204,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0)) ),
    inference(backward_demodulation,[],[f153,f203])).

fof(f203,plain,(
    ! [X1] : k3_xboole_0(sK2,X1) = k1_relat_1(k7_relat_1(sK4,X1)) ),
    inference(backward_demodulation,[],[f152,f202])).

fof(f202,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f201,f112])).

fof(f112,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f82,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f201,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f200,f116])).

fof(f116,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f83,f52])).

fof(f200,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f144,f80])).

fof(f144,plain,(
    v1_partfun1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f143,f51])).

fof(f51,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f143,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f142,f50])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f142,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f138,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2) ),
    inference(resolution,[],[f74,f52])).

fof(f152,plain,(
    ! [X1] : k3_xboole_0(k1_relat_1(sK4),X1) = k1_relat_1(k7_relat_1(sK4,X1)) ),
    inference(resolution,[],[f112,f75])).

fof(f153,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0))) ),
    inference(backward_demodulation,[],[f151,f152])).

fof(f151,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0)) ),
    inference(resolution,[],[f112,f76])).

fof(f500,plain,
    ( k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f499,f132])).

fof(f132,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(resolution,[],[f81,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f499,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f498,f48])).

fof(f498,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f497,f47])).

fof(f497,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f496,f54])).

fof(f496,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f494,f53])).

fof(f494,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(resolution,[],[f307,f49])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X0))
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2) ) ),
    inference(forward_demodulation,[],[f306,f149])).

fof(f149,plain,(
    ! [X1] : k2_partfun1(sK2,sK1,sK4,X1) = k7_relat_1(sK4,X1) ),
    inference(subsumption_resolution,[],[f146,f50])).

fof(f146,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK4)
      | k2_partfun1(sK2,sK1,sK4,X1) = k7_relat_1(sK4,X1) ) ),
    inference(resolution,[],[f84,f52])).

fof(f306,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f305,f58])).

fof(f305,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f304,f51])).

fof(f304,plain,(
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
    inference(subsumption_resolution,[],[f303,f50])).

fof(f303,plain,(
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
    inference(resolution,[],[f185,f52])).

fof(f185,plain,(
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
    inference(subsumption_resolution,[],[f184,f59])).

fof(f59,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f184,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_xboole_0(X4)
      | v1_xboole_0(sK0)
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
    inference(subsumption_resolution,[],[f179,f56])).

fof(f179,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_xboole_0(X4)
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK0)
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
    inference(resolution,[],[f97,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
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
    inference(subsumption_resolution,[],[f95,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f95,plain,(
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
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(subsumption_resolution,[],[f93,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
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
    inference(subsumption_resolution,[],[f91,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f353,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f205,f350])).

fof(f205,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f150,f204])).

fof(f150,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) ),
    inference(backward_demodulation,[],[f148,f149])).

fof(f148,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f136,f147])).

fof(f136,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f46,f132])).

fof(f46,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f529,plain,
    ( k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f528,f350])).

fof(f528,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f527,f147])).

fof(f527,plain,
    ( k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f526,f204])).

fof(f526,plain,
    ( k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(forward_demodulation,[],[f525,f132])).

fof(f525,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f524,f48])).

fof(f524,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f523,f47])).

fof(f523,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f522,f54])).

fof(f522,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f520,f53])).

fof(f520,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(resolution,[],[f317,f49])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X0))
      | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1 ) ),
    inference(forward_demodulation,[],[f316,f149])).

fof(f316,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1 ) ),
    inference(subsumption_resolution,[],[f315,f58])).

fof(f315,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0))
      | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1 ) ),
    inference(subsumption_resolution,[],[f314,f51])).

fof(f314,plain,(
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
    inference(subsumption_resolution,[],[f313,f50])).

fof(f313,plain,(
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
    inference(resolution,[],[f193,f52])).

fof(f193,plain,(
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
    inference(subsumption_resolution,[],[f192,f59])).

fof(f192,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_xboole_0(X4)
      | v1_xboole_0(sK0)
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
    inference(subsumption_resolution,[],[f187,f56])).

fof(f187,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_xboole_0(X4)
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK0)
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
    inference(resolution,[],[f98,f57])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
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
    inference(subsumption_resolution,[],[f96,f85])).

fof(f96,plain,(
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
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f94,f86])).

fof(f94,plain,(
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
    inference(subsumption_resolution,[],[f90,f87])).

fof(f90,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f588,plain,(
    k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    inference(resolution,[],[f269,f337])).

fof(f337,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(resolution,[],[f218,f125])).

fof(f218,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(resolution,[],[f104,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f104,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f69,f68])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f269,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f267,f112])).

fof(f267,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = k7_relat_1(sK4,X0) ) ),
    inference(superposition,[],[f67,f202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:20:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (2993)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (3020)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.45  % (2995)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (3017)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (2995)Refutation not found, incomplete strategy% (2995)------------------------------
% 0.21/0.46  % (2995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.47  % (2995)Memory used [KB]: 10746
% 0.21/0.47  % (2995)Time elapsed: 0.013 s
% 0.21/0.47  % (2995)------------------------------
% 0.21/0.47  % (2995)------------------------------
% 0.21/0.48  % (2999)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (3012)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (3004)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (3016)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (3008)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (3010)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (2997)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (3002)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (3009)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (3018)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (3013)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (3011)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (3019)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (3021)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (3021)Refutation not found, incomplete strategy% (3021)------------------------------
% 0.21/0.51  % (3021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3021)Memory used [KB]: 10618
% 0.21/0.51  % (3021)Time elapsed: 0.095 s
% 0.21/0.51  % (3021)------------------------------
% 0.21/0.51  % (3021)------------------------------
% 0.21/0.51  % (3014)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (3015)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (3007)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  % (3018)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 1.48/0.55  % SZS output start Proof for theBenchmark
% 1.48/0.55  fof(f589,plain,(
% 1.48/0.55    $false),
% 1.48/0.55    inference(subsumption_resolution,[],[f588,f577])).
% 1.48/0.55  fof(f577,plain,(
% 1.48/0.55    k1_xboole_0 != k7_relat_1(sK4,sK3)),
% 1.48/0.55    inference(backward_demodulation,[],[f530,f576])).
% 1.48/0.55  fof(f576,plain,(
% 1.48/0.55    k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 1.48/0.55    inference(resolution,[],[f235,f125])).
% 1.48/0.55  fof(f125,plain,(
% 1.48/0.55    r1_xboole_0(sK2,sK3)),
% 1.48/0.55    inference(subsumption_resolution,[],[f124,f56])).
% 1.48/0.55  fof(f56,plain,(
% 1.48/0.55    ~v1_xboole_0(sK2)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f25,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.48/0.55    inference(flattening,[],[f24])).
% 1.48/0.55  fof(f24,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f20])).
% 1.48/0.55  fof(f20,negated_conjecture,(
% 1.48/0.55    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.48/0.55    inference(negated_conjecture,[],[f19])).
% 1.48/0.55  fof(f19,conjecture,(
% 1.48/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.48/0.55  fof(f124,plain,(
% 1.48/0.55    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f123,f53])).
% 1.48/0.55  fof(f53,plain,(
% 1.48/0.55    ~v1_xboole_0(sK3)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f123,plain,(
% 1.48/0.55    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 1.48/0.55    inference(resolution,[],[f78,f55])).
% 1.48/0.55  fof(f55,plain,(
% 1.48/0.55    r1_subset_1(sK2,sK3)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f78,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f36])).
% 1.48/0.55  fof(f36,plain,(
% 1.48/0.55    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.48/0.55    inference(flattening,[],[f35])).
% 1.48/0.55  fof(f35,plain,(
% 1.48/0.55    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f11])).
% 1.48/0.55  fof(f11,axiom,(
% 1.48/0.55    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.48/0.55  fof(f235,plain,(
% 1.48/0.55    ( ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f233,f111])).
% 1.48/0.55  fof(f111,plain,(
% 1.48/0.55    v1_relat_1(sK5)),
% 1.48/0.55    inference(resolution,[],[f82,f49])).
% 1.48/0.55  fof(f49,plain,(
% 1.48/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f82,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f40])).
% 1.48/0.55  fof(f40,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(ennf_transformation,[],[f12])).
% 1.48/0.55  fof(f12,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.55  fof(f233,plain,(
% 1.48/0.55    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) )),
% 1.48/0.55    inference(superposition,[],[f67,f197])).
% 1.48/0.55  fof(f197,plain,(
% 1.48/0.55    sK3 = k1_relat_1(sK5)),
% 1.48/0.55    inference(subsumption_resolution,[],[f196,f111])).
% 1.48/0.55  fof(f196,plain,(
% 1.48/0.55    sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5)),
% 1.48/0.55    inference(subsumption_resolution,[],[f195,f115])).
% 1.48/0.55  fof(f115,plain,(
% 1.48/0.55    v4_relat_1(sK5,sK3)),
% 1.48/0.55    inference(resolution,[],[f83,f49])).
% 1.48/0.55  fof(f83,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f41])).
% 1.48/0.55  fof(f41,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(ennf_transformation,[],[f23])).
% 1.48/0.55  fof(f23,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.48/0.55    inference(pure_predicate_removal,[],[f13])).
% 1.48/0.55  fof(f13,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.48/0.55  fof(f195,plain,(
% 1.48/0.55    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5)),
% 1.48/0.55    inference(resolution,[],[f141,f80])).
% 1.48/0.55  fof(f80,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f38])).
% 1.48/0.55  fof(f38,plain,(
% 1.48/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(flattening,[],[f37])).
% 1.48/0.55  fof(f37,plain,(
% 1.48/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.48/0.55    inference(ennf_transformation,[],[f15])).
% 1.48/0.55  fof(f15,axiom,(
% 1.48/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.48/0.55  fof(f141,plain,(
% 1.48/0.55    v1_partfun1(sK5,sK3)),
% 1.48/0.55    inference(subsumption_resolution,[],[f140,f48])).
% 1.48/0.55  fof(f48,plain,(
% 1.48/0.55    v1_funct_2(sK5,sK3,sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f140,plain,(
% 1.48/0.55    ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3)),
% 1.48/0.55    inference(subsumption_resolution,[],[f139,f47])).
% 1.48/0.55  fof(f47,plain,(
% 1.48/0.55    v1_funct_1(sK5)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f139,plain,(
% 1.48/0.55    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3)),
% 1.48/0.55    inference(subsumption_resolution,[],[f137,f58])).
% 1.48/0.55  fof(f58,plain,(
% 1.48/0.55    ~v1_xboole_0(sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f137,plain,(
% 1.48/0.55    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3)),
% 1.48/0.55    inference(resolution,[],[f74,f49])).
% 1.48/0.55  fof(f74,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f32])).
% 1.48/0.55  fof(f32,plain,(
% 1.48/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.48/0.55    inference(flattening,[],[f31])).
% 1.48/0.55  fof(f31,plain,(
% 1.48/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f14])).
% 1.48/0.55  fof(f14,axiom,(
% 1.48/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.48/0.55  fof(f67,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f28])).
% 1.48/0.55  fof(f28,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f7])).
% 1.48/0.55  fof(f7,axiom,(
% 1.48/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 1.48/0.55  fof(f530,plain,(
% 1.48/0.55    k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f529,f504])).
% 1.48/0.55  fof(f504,plain,(
% 1.48/0.55    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f353,f503])).
% 1.48/0.55  fof(f503,plain,(
% 1.48/0.55    k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(forward_demodulation,[],[f502,f350])).
% 1.48/0.55  fof(f350,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(X0,sK3))) )),
% 1.48/0.55    inference(superposition,[],[f199,f68])).
% 1.48/0.55  fof(f68,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f1])).
% 1.48/0.55  fof(f1,axiom,(
% 1.48/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.48/0.55  fof(f199,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(sK3,X0))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f131,f198])).
% 1.48/0.55  fof(f198,plain,(
% 1.48/0.55    ( ! [X0] : (k1_relat_1(k7_relat_1(sK5,X0)) = k3_xboole_0(sK3,X0)) )),
% 1.48/0.55    inference(backward_demodulation,[],[f129,f197])).
% 1.48/0.55  fof(f129,plain,(
% 1.48/0.55    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK5),X0) = k1_relat_1(k7_relat_1(sK5,X0))) )),
% 1.48/0.55    inference(resolution,[],[f75,f111])).
% 1.48/0.55  fof(f75,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f33])).
% 1.48/0.55  fof(f33,plain,(
% 1.48/0.55    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f10])).
% 1.48/0.55  fof(f10,axiom,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.48/0.55  fof(f131,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0)))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f130,f129])).
% 1.48/0.55  fof(f130,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0))) )),
% 1.48/0.55    inference(resolution,[],[f76,f111])).
% 1.48/0.55  fof(f76,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f34])).
% 1.48/0.55  fof(f34,plain,(
% 1.48/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f8])).
% 1.48/0.55  fof(f8,axiom,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 1.48/0.55  fof(f502,plain,(
% 1.48/0.55    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(forward_demodulation,[],[f501,f147])).
% 1.48/0.55  fof(f147,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f145,f47])).
% 1.48/0.55  fof(f145,plain,(
% 1.48/0.55    ( ! [X0] : (~v1_funct_1(sK5) | k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) )),
% 1.48/0.55    inference(resolution,[],[f84,f49])).
% 1.48/0.55  fof(f84,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f43])).
% 1.48/0.55  fof(f43,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.48/0.55    inference(flattening,[],[f42])).
% 1.48/0.55  fof(f42,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.48/0.55    inference(ennf_transformation,[],[f16])).
% 1.48/0.55  fof(f16,axiom,(
% 1.48/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.48/0.55  fof(f501,plain,(
% 1.48/0.55    k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(forward_demodulation,[],[f500,f204])).
% 1.48/0.55  fof(f204,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f153,f203])).
% 1.48/0.55  fof(f203,plain,(
% 1.48/0.55    ( ! [X1] : (k3_xboole_0(sK2,X1) = k1_relat_1(k7_relat_1(sK4,X1))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f152,f202])).
% 1.48/0.55  fof(f202,plain,(
% 1.48/0.55    sK2 = k1_relat_1(sK4)),
% 1.48/0.55    inference(subsumption_resolution,[],[f201,f112])).
% 1.48/0.55  fof(f112,plain,(
% 1.48/0.55    v1_relat_1(sK4)),
% 1.48/0.55    inference(resolution,[],[f82,f52])).
% 1.48/0.55  fof(f52,plain,(
% 1.48/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f201,plain,(
% 1.48/0.55    sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 1.48/0.55    inference(subsumption_resolution,[],[f200,f116])).
% 1.48/0.55  fof(f116,plain,(
% 1.48/0.55    v4_relat_1(sK4,sK2)),
% 1.48/0.55    inference(resolution,[],[f83,f52])).
% 1.48/0.55  fof(f200,plain,(
% 1.48/0.55    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 1.48/0.55    inference(resolution,[],[f144,f80])).
% 1.48/0.55  fof(f144,plain,(
% 1.48/0.55    v1_partfun1(sK4,sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f143,f51])).
% 1.48/0.55  fof(f51,plain,(
% 1.48/0.55    v1_funct_2(sK4,sK2,sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f143,plain,(
% 1.48/0.55    ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f142,f50])).
% 1.48/0.55  fof(f50,plain,(
% 1.48/0.55    v1_funct_1(sK4)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f142,plain,(
% 1.48/0.55    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f138,f58])).
% 1.48/0.55  fof(f138,plain,(
% 1.48/0.55    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2)),
% 1.48/0.55    inference(resolution,[],[f74,f52])).
% 1.48/0.55  fof(f152,plain,(
% 1.48/0.55    ( ! [X1] : (k3_xboole_0(k1_relat_1(sK4),X1) = k1_relat_1(k7_relat_1(sK4,X1))) )),
% 1.48/0.55    inference(resolution,[],[f112,f75])).
% 1.48/0.55  fof(f153,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0)))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f151,f152])).
% 1.48/0.55  fof(f151,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0))) )),
% 1.48/0.55    inference(resolution,[],[f112,f76])).
% 1.48/0.55  fof(f500,plain,(
% 1.48/0.55    k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(forward_demodulation,[],[f499,f132])).
% 1.48/0.55  fof(f132,plain,(
% 1.48/0.55    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)) )),
% 1.48/0.55    inference(resolution,[],[f81,f54])).
% 1.48/0.55  fof(f54,plain,(
% 1.48/0.55    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f81,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f39])).
% 1.48/0.55  fof(f39,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f6])).
% 1.48/0.55  fof(f6,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.48/0.55  fof(f499,plain,(
% 1.48/0.55    k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f498,f48])).
% 1.48/0.55  fof(f498,plain,(
% 1.48/0.55    ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f497,f47])).
% 1.48/0.55  fof(f497,plain,(
% 1.48/0.55    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f496,f54])).
% 1.48/0.55  fof(f496,plain,(
% 1.48/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(subsumption_resolution,[],[f494,f53])).
% 1.48/0.55  fof(f494,plain,(
% 1.48/0.55    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(resolution,[],[f307,f49])).
% 1.48/0.55  fof(f307,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 1.48/0.55    inference(forward_demodulation,[],[f306,f149])).
% 1.48/0.55  fof(f149,plain,(
% 1.48/0.55    ( ! [X1] : (k2_partfun1(sK2,sK1,sK4,X1) = k7_relat_1(sK4,X1)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f146,f50])).
% 1.48/0.55  fof(f146,plain,(
% 1.48/0.55    ( ! [X1] : (~v1_funct_1(sK4) | k2_partfun1(sK2,sK1,sK4,X1) = k7_relat_1(sK4,X1)) )),
% 1.48/0.55    inference(resolution,[],[f84,f52])).
% 1.48/0.55  fof(f306,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f305,f58])).
% 1.48/0.55  fof(f305,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f304,f51])).
% 1.48/0.55  fof(f304,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f303,f50])).
% 1.48/0.55  fof(f303,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),sK2)) )),
% 1.48/0.55    inference(resolution,[],[f185,f52])).
% 1.48/0.55  fof(f185,plain,(
% 1.48/0.55    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | v1_xboole_0(X4) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),sK2) = X6) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f184,f59])).
% 1.48/0.55  fof(f59,plain,(
% 1.48/0.55    ~v1_xboole_0(sK0)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f184,plain,(
% 1.48/0.55    ( ! [X6,X4,X7,X5] : (v1_xboole_0(X4) | v1_xboole_0(sK0) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),sK2) = X6) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f179,f56])).
% 1.48/0.55  fof(f179,plain,(
% 1.48/0.55    ( ! [X6,X4,X7,X5] : (v1_xboole_0(X4) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),sK2) = X6) )),
% 1.48/0.55    inference(resolution,[],[f97,f57])).
% 1.48/0.55  fof(f57,plain,(
% 1.48/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f97,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f95,f85])).
% 1.48/0.55  fof(f85,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f45])).
% 1.48/0.55  fof(f45,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.48/0.55    inference(flattening,[],[f44])).
% 1.48/0.55  fof(f44,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f18])).
% 1.48/0.55  fof(f18,axiom,(
% 1.48/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.48/0.55  fof(f95,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f93,f86])).
% 1.48/0.55  fof(f86,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f45])).
% 1.48/0.55  fof(f93,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f91,f87])).
% 1.48/0.55  fof(f87,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f45])).
% 1.48/0.55  fof(f91,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.48/0.55    inference(equality_resolution,[],[f64])).
% 1.48/0.55  fof(f64,plain,(
% 1.48/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.48/0.55    inference(cnf_transformation,[],[f27])).
% 1.48/0.55  fof(f27,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.48/0.55    inference(flattening,[],[f26])).
% 1.48/0.55  fof(f26,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f17])).
% 1.48/0.55  fof(f17,axiom,(
% 1.48/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.48/0.55  fof(f353,plain,(
% 1.48/0.55    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(backward_demodulation,[],[f205,f350])).
% 1.48/0.55  fof(f205,plain,(
% 1.48/0.55    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.48/0.55    inference(backward_demodulation,[],[f150,f204])).
% 1.48/0.55  fof(f150,plain,(
% 1.48/0.55    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))),
% 1.48/0.55    inference(backward_demodulation,[],[f148,f149])).
% 1.48/0.55  fof(f148,plain,(
% 1.48/0.55    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(backward_demodulation,[],[f136,f147])).
% 1.48/0.55  fof(f136,plain,(
% 1.48/0.55    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(backward_demodulation,[],[f46,f132])).
% 1.48/0.55  fof(f46,plain,(
% 1.48/0.55    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f529,plain,(
% 1.48/0.55    k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(forward_demodulation,[],[f528,f350])).
% 1.48/0.55  fof(f528,plain,(
% 1.48/0.55    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(forward_demodulation,[],[f527,f147])).
% 1.48/0.55  fof(f527,plain,(
% 1.48/0.55    k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(forward_demodulation,[],[f526,f204])).
% 1.48/0.55  fof(f526,plain,(
% 1.48/0.55    k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(forward_demodulation,[],[f525,f132])).
% 1.48/0.55  fof(f525,plain,(
% 1.48/0.55    k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(subsumption_resolution,[],[f524,f48])).
% 1.48/0.55  fof(f524,plain,(
% 1.48/0.55    ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(subsumption_resolution,[],[f523,f47])).
% 1.48/0.55  fof(f523,plain,(
% 1.48/0.55    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(subsumption_resolution,[],[f522,f54])).
% 1.48/0.55  fof(f522,plain,(
% 1.48/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(subsumption_resolution,[],[f520,f53])).
% 1.48/0.55  fof(f520,plain,(
% 1.48/0.55    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.48/0.55    inference(resolution,[],[f317,f49])).
% 1.48/0.55  fof(f317,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 1.48/0.55    inference(forward_demodulation,[],[f316,f149])).
% 1.48/0.55  fof(f316,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f315,f58])).
% 1.48/0.55  fof(f315,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f314,f51])).
% 1.48/0.55  fof(f314,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f313,f50])).
% 1.48/0.55  fof(f313,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,X0)) != k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,sK2,X0)) | k2_partfun1(k4_subset_1(sK0,sK2,X0),sK1,k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),X0) = X1) )),
% 1.48/0.55    inference(resolution,[],[f193,f52])).
% 1.48/0.55  fof(f193,plain,(
% 1.48/0.55    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | v1_xboole_0(X4) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),X5) = X7) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f192,f59])).
% 1.48/0.55  fof(f192,plain,(
% 1.48/0.55    ( ! [X6,X4,X7,X5] : (v1_xboole_0(X4) | v1_xboole_0(sK0) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),X5) = X7) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f187,f56])).
% 1.48/0.55  fof(f187,plain,(
% 1.48/0.55    ( ! [X6,X4,X7,X5] : (v1_xboole_0(X4) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X5) | ~m1_subset_1(X5,k1_zfmisc_1(sK0)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK2,X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK2,X4))) | ~v1_funct_1(X7) | ~v1_funct_2(X7,X5,X4) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | k2_partfun1(sK2,X4,X6,k9_subset_1(sK0,sK2,X5)) != k2_partfun1(X5,X4,X7,k9_subset_1(sK0,sK2,X5)) | k2_partfun1(k4_subset_1(sK0,sK2,X5),X4,k1_tmap_1(sK0,X4,sK2,X5,X6,X7),X5) = X7) )),
% 1.48/0.55    inference(resolution,[],[f98,f57])).
% 1.48/0.55  fof(f98,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f96,f85])).
% 1.48/0.55  fof(f96,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f94,f86])).
% 1.48/0.55  fof(f94,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f90,f87])).
% 1.48/0.55  fof(f90,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.48/0.55    inference(equality_resolution,[],[f65])).
% 1.48/0.55  fof(f65,plain,(
% 1.48/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.48/0.55    inference(cnf_transformation,[],[f27])).
% 1.48/0.55  fof(f588,plain,(
% 1.48/0.55    k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 1.48/0.55    inference(resolution,[],[f269,f337])).
% 1.48/0.55  fof(f337,plain,(
% 1.48/0.55    r1_xboole_0(sK3,sK2)),
% 1.48/0.55    inference(resolution,[],[f218,f125])).
% 1.48/0.55  fof(f218,plain,(
% 1.48/0.55    ( ! [X6,X7] : (~r1_xboole_0(X6,X7) | r1_xboole_0(X7,X6)) )),
% 1.48/0.55    inference(resolution,[],[f104,f70])).
% 1.48/0.55  fof(f70,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f29])).
% 1.48/0.55  fof(f29,plain,(
% 1.48/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.48/0.55    inference(ennf_transformation,[],[f21])).
% 1.48/0.55  fof(f21,plain,(
% 1.48/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.55    inference(rectify,[],[f3])).
% 1.48/0.55  fof(f3,axiom,(
% 1.48/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.48/0.55  fof(f104,plain,(
% 1.48/0.55    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | ~r1_xboole_0(X2,X3)) )),
% 1.48/0.55    inference(superposition,[],[f69,f68])).
% 1.48/0.55  fof(f69,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f29])).
% 1.48/0.55  fof(f269,plain,(
% 1.48/0.55    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f267,f112])).
% 1.48/0.55  fof(f267,plain,(
% 1.48/0.55    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) )),
% 1.48/0.55    inference(superposition,[],[f67,f202])).
% 1.48/0.55  % SZS output end Proof for theBenchmark
% 1.48/0.55  % (3018)------------------------------
% 1.48/0.55  % (3018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (3018)Termination reason: Refutation
% 1.48/0.55  
% 1.48/0.55  % (3018)Memory used [KB]: 2174
% 1.48/0.55  % (3018)Time elapsed: 0.133 s
% 1.48/0.55  % (3018)------------------------------
% 1.48/0.55  % (3018)------------------------------
% 1.48/0.56  % (2991)Success in time 0.201 s
%------------------------------------------------------------------------------

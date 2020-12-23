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
% DateTime   : Thu Dec  3 13:17:33 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 590 expanded)
%              Number of leaves         :   14 ( 120 expanded)
%              Depth                    :   26
%              Number of atoms          :  823 (4951 expanded)
%              Number of equality atoms :  155 ( 883 expanded)
%              Maximal formula depth    :   34 (   9 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(global_subsumption,[],[f177,f551,f629])).

fof(f629,plain,(
    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f628,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f628,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f627,f37])).

fof(f37,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f627,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f626,f36])).

% (25426)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f626,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f625,f113])).

fof(f113,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(resolution,[],[f107,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f107,plain,(
    v1_xboole_0(k7_relat_1(sK4,k1_xboole_0)) ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f84,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k7_relat_1(sK4,X1)) ) ),
    inference(resolution,[],[f80,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f80,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f61,f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f625,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(superposition,[],[f624,f175])).

fof(f175,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    inference(resolution,[],[f171,f38])).

fof(f171,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k2_partfun1(X3,X4,sK4,X5) = k7_relat_1(sK4,X5) ) ),
    inference(resolution,[],[f62,f36])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f624,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(forward_demodulation,[],[f623,f92])).

fof(f92,plain,(
    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    inference(resolution,[],[f88,f50])).

fof(f88,plain,(
    v1_xboole_0(k7_relat_1(sK5,k1_xboole_0)) ),
    inference(resolution,[],[f82,f46])).

fof(f82,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k7_relat_1(sK5,X1)) ) ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f623,plain,(
    ! [X1] :
      ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(forward_demodulation,[],[f622,f167])).

fof(f167,plain,(
    k1_xboole_0 = k9_subset_1(sK0,sK2,sK3) ),
    inference(superposition,[],[f163,f161])).

fof(f161,plain,(
    k1_xboole_0 = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f67,f160])).

fof(f160,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f159,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f159,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f156,f39])).

fof(f39,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f156,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f163,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK3)) ),
    inference(resolution,[],[f69,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f622,plain,(
    ! [X1] :
      ( k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(subsumption_resolution,[],[f620,f42])).

fof(f620,plain,(
    ! [X1] :
      ( k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_xboole_0(sK2)
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    inference(resolution,[],[f618,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f618,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1 ) ),
    inference(resolution,[],[f617,f40])).

fof(f617,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X1,X0,sK3))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2 ) ),
    inference(forward_demodulation,[],[f616,f172])).

fof(f172,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) ),
    inference(resolution,[],[f170,f35])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ) ),
    inference(resolution,[],[f62,f33])).

fof(f33,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f17])).

fof(f616,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2 ) ),
    inference(subsumption_resolution,[],[f615,f34])).

fof(f34,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f615,plain,(
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
    inference(subsumption_resolution,[],[f614,f44])).

fof(f44,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f614,plain,(
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
    inference(subsumption_resolution,[],[f613,f39])).

fof(f613,plain,(
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
    inference(resolution,[],[f595,f35])).

fof(f595,plain,(
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
    inference(resolution,[],[f343,f33])).

fof(f343,plain,(
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
    inference(subsumption_resolution,[],[f342,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
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
    inference(subsumption_resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f342,plain,(
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
    inference(subsumption_resolution,[],[f341,f75])).

fof(f75,plain,(
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
    inference(subsumption_resolution,[],[f64,f51])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f341,plain,(
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
    inference(subsumption_resolution,[],[f340,f51])).

fof(f340,plain,(
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
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,(
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
    inference(resolution,[],[f73,f76])).

fof(f76,plain,(
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
    inference(subsumption_resolution,[],[f63,f51])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f551,plain,(
    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f550,f38])).

fof(f550,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f549,f37])).

fof(f549,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f548,f36])).

fof(f548,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f547,f113])).

fof(f547,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(superposition,[],[f546,f175])).

fof(f546,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(forward_demodulation,[],[f545,f92])).

fof(f545,plain,(
    ! [X1] :
      ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,X1,k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(forward_demodulation,[],[f544,f167])).

fof(f544,plain,(
    ! [X1] :
      ( k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(subsumption_resolution,[],[f542,f42])).

fof(f542,plain,(
    ! [X1] :
      ( k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_xboole_0(sK2)
      | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    inference(resolution,[],[f540,f43])).

fof(f540,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) ) ),
    inference(resolution,[],[f539,f40])).

fof(f539,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X1,X0,sK3))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3) ) ),
    inference(forward_demodulation,[],[f538,f172])).

fof(f538,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | v1_xboole_0(X0)
      | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3))
      | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3) ) ),
    inference(subsumption_resolution,[],[f537,f34])).

fof(f537,plain,(
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
    inference(subsumption_resolution,[],[f536,f44])).

fof(f536,plain,(
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
    inference(subsumption_resolution,[],[f535,f39])).

fof(f535,plain,(
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
    inference(resolution,[],[f503,f35])).

fof(f503,plain,(
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
    inference(resolution,[],[f206,f33])).

fof(f206,plain,(
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
    inference(subsumption_resolution,[],[f205,f74])).

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
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f204,f75])).

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
      | ~ v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0)
      | ~ m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0)))
      | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5 ) ),
    inference(subsumption_resolution,[],[f203,f51])).

fof(f203,plain,(
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
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
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
    inference(resolution,[],[f72,f76])).

fof(f72,plain,(
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
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f19])).

% (25429)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f177,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f176,f113])).

fof(f176,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f174,f175])).

fof(f174,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f173,f92])).

fof(f173,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f169,f172])).

fof(f169,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(backward_demodulation,[],[f32,f167])).

fof(f32,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f17])).

% (25427)Refutation not found, incomplete strategy% (25427)------------------------------
% (25427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25427)Termination reason: Refutation not found, incomplete strategy

% (25427)Memory used [KB]: 2174
% (25427)Time elapsed: 0.153 s
% (25427)------------------------------
% (25427)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (25428)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (25406)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (25423)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (25411)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (25423)Refutation not found, incomplete strategy% (25423)------------------------------
% 0.21/0.51  % (25423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25407)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (25423)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25423)Memory used [KB]: 10746
% 0.21/0.51  % (25423)Time elapsed: 0.066 s
% 0.21/0.51  % (25423)------------------------------
% 0.21/0.51  % (25423)------------------------------
% 0.21/0.51  % (25413)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (25408)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (25421)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (25430)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (25410)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (25409)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (25431)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (25427)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (25428)Refutation not found, incomplete strategy% (25428)------------------------------
% 0.21/0.52  % (25428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25428)Memory used [KB]: 11385
% 0.21/0.52  % (25428)Time elapsed: 0.069 s
% 0.21/0.52  % (25428)------------------------------
% 0.21/0.52  % (25428)------------------------------
% 0.21/0.53  % (25425)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (25417)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (25416)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.53  % (25414)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.53  % (25418)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.53  % (25432)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.53  % (25424)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.54  % (25420)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.54  % (25436)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.54  % (25434)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.55  % (25412)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.55  % (25422)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.56  % (25419)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.56  % (25405)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.57  % (25411)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f630,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(global_subsumption,[],[f177,f551,f629])).
% 1.47/0.57  fof(f629,plain,(
% 1.47/0.57    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.47/0.57    inference(subsumption_resolution,[],[f628,f38])).
% 1.47/0.57  fof(f38,plain,(
% 1.47/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f17,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f16])).
% 1.47/0.57  fof(f16,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f15])).
% 1.47/0.57  fof(f15,negated_conjecture,(
% 1.47/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.47/0.57    inference(negated_conjecture,[],[f14])).
% 1.47/0.57  fof(f14,conjecture,(
% 1.47/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.47/0.57  fof(f628,plain,(
% 1.47/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.47/0.57    inference(subsumption_resolution,[],[f627,f37])).
% 1.47/0.57  fof(f37,plain,(
% 1.47/0.57    v1_funct_2(sK4,sK2,sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f627,plain,(
% 1.47/0.57    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.47/0.57    inference(subsumption_resolution,[],[f626,f36])).
% 1.47/0.57  % (25426)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.57  fof(f36,plain,(
% 1.47/0.57    v1_funct_1(sK4)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f626,plain,(
% 1.47/0.57    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.47/0.57    inference(subsumption_resolution,[],[f625,f113])).
% 1.47/0.57  fof(f113,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.47/0.57    inference(resolution,[],[f107,f50])).
% 1.47/0.57  fof(f50,plain,(
% 1.47/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.47/0.57    inference(cnf_transformation,[],[f20])).
% 1.47/0.57  fof(f20,plain,(
% 1.47/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f3])).
% 1.47/0.57  fof(f3,axiom,(
% 1.47/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.47/0.57  fof(f107,plain,(
% 1.47/0.57    v1_xboole_0(k7_relat_1(sK4,k1_xboole_0))),
% 1.47/0.57    inference(resolution,[],[f84,f46])).
% 1.47/0.57  fof(f46,plain,(
% 1.47/0.57    v1_xboole_0(k1_xboole_0)),
% 1.47/0.57    inference(cnf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    v1_xboole_0(k1_xboole_0)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.47/0.57  fof(f84,plain,(
% 1.47/0.57    ( ! [X1] : (~v1_xboole_0(X1) | v1_xboole_0(k7_relat_1(sK4,X1))) )),
% 1.47/0.57    inference(resolution,[],[f80,f56])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_xboole_0(X1) | v1_xboole_0(k7_relat_1(X0,X1))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f25])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(flattening,[],[f24])).
% 1.47/0.57  fof(f24,plain,(
% 1.47/0.57    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f8])).
% 1.47/0.57  fof(f8,axiom,(
% 1.47/0.57    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).
% 1.47/0.57  fof(f80,plain,(
% 1.47/0.57    v1_relat_1(sK4)),
% 1.47/0.57    inference(resolution,[],[f61,f38])).
% 1.47/0.57  fof(f61,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  fof(f27,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(ennf_transformation,[],[f10])).
% 1.47/0.57  fof(f10,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.47/0.57  fof(f625,plain,(
% 1.47/0.57    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.47/0.57    inference(superposition,[],[f624,f175])).
% 1.47/0.57  fof(f175,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) )),
% 1.47/0.57    inference(resolution,[],[f171,f38])).
% 1.47/0.57  fof(f171,plain,(
% 1.47/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_partfun1(X3,X4,sK4,X5) = k7_relat_1(sK4,X5)) )),
% 1.47/0.57    inference(resolution,[],[f62,f36])).
% 1.47/0.57  fof(f62,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f29])).
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.47/0.57    inference(flattening,[],[f28])).
% 1.47/0.57  fof(f28,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.47/0.57    inference(ennf_transformation,[],[f11])).
% 1.47/0.57  fof(f11,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.47/0.57  fof(f624,plain,(
% 1.47/0.57    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 1.47/0.57    inference(forward_demodulation,[],[f623,f92])).
% 1.47/0.57  fof(f92,plain,(
% 1.47/0.57    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.47/0.57    inference(resolution,[],[f88,f50])).
% 1.47/0.57  fof(f88,plain,(
% 1.47/0.57    v1_xboole_0(k7_relat_1(sK5,k1_xboole_0))),
% 1.47/0.57    inference(resolution,[],[f82,f46])).
% 1.47/0.57  fof(f82,plain,(
% 1.47/0.57    ( ! [X1] : (~v1_xboole_0(X1) | v1_xboole_0(k7_relat_1(sK5,X1))) )),
% 1.47/0.57    inference(resolution,[],[f79,f56])).
% 1.47/0.57  fof(f79,plain,(
% 1.47/0.57    v1_relat_1(sK5)),
% 1.47/0.57    inference(resolution,[],[f61,f35])).
% 1.47/0.57  fof(f35,plain,(
% 1.47/0.57    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f623,plain,(
% 1.47/0.57    ( ! [X1] : (k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 1.47/0.57    inference(forward_demodulation,[],[f622,f167])).
% 1.47/0.57  fof(f167,plain,(
% 1.47/0.57    k1_xboole_0 = k9_subset_1(sK0,sK2,sK3)),
% 1.47/0.57    inference(superposition,[],[f163,f161])).
% 1.47/0.57  fof(f161,plain,(
% 1.47/0.57    k1_xboole_0 = k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.47/0.57    inference(resolution,[],[f67,f160])).
% 1.47/0.57  fof(f160,plain,(
% 1.47/0.57    r1_xboole_0(sK2,sK3)),
% 1.47/0.57    inference(subsumption_resolution,[],[f159,f42])).
% 1.47/0.57  fof(f42,plain,(
% 1.47/0.57    ~v1_xboole_0(sK2)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f159,plain,(
% 1.47/0.57    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 1.47/0.57    inference(subsumption_resolution,[],[f156,f39])).
% 1.47/0.57  fof(f39,plain,(
% 1.47/0.57    ~v1_xboole_0(sK3)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f156,plain,(
% 1.47/0.57    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 1.47/0.57    inference(resolution,[],[f55,f41])).
% 1.47/0.57  fof(f41,plain,(
% 1.47/0.57    r1_subset_1(sK2,sK3)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f55,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f23])).
% 1.47/0.57  fof(f23,plain,(
% 1.47/0.57    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f22])).
% 1.47/0.57  fof(f22,plain,(
% 1.47/0.57    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f9])).
% 1.47/0.57  fof(f9,axiom,(
% 1.47/0.57    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.47/0.57  fof(f67,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.47/0.57    inference(definition_unfolding,[],[f59,f66])).
% 1.47/0.57  fof(f66,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.47/0.57    inference(definition_unfolding,[],[f52,f53])).
% 1.47/0.57  fof(f53,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 1.47/0.57  fof(f52,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f7])).
% 1.47/0.57  fof(f7,axiom,(
% 1.47/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.47/0.57  fof(f59,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f1])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.47/0.57  fof(f163,plain,(
% 1.47/0.57    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK3))) )),
% 1.47/0.57    inference(resolution,[],[f69,f40])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f69,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) )),
% 1.47/0.57    inference(definition_unfolding,[],[f60,f66])).
% 1.47/0.57  fof(f60,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f26])).
% 1.47/0.57  fof(f26,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f5])).
% 1.47/0.57  fof(f5,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.47/0.57  fof(f622,plain,(
% 1.47/0.57    ( ! [X1] : (k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f620,f42])).
% 1.47/0.57  fof(f620,plain,(
% 1.47/0.57    ( ! [X1] : (k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | v1_xboole_0(sK2) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) )),
% 1.47/0.57    inference(resolution,[],[f618,f43])).
% 1.47/0.57  fof(f43,plain,(
% 1.47/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f618,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1) )),
% 1.47/0.57    inference(resolution,[],[f617,f40])).
% 1.47/0.57  fof(f617,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X1,X0,sK3)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 1.47/0.57    inference(forward_demodulation,[],[f616,f172])).
% 1.47/0.57  fof(f172,plain,(
% 1.47/0.57    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) )),
% 1.47/0.57    inference(resolution,[],[f170,f35])).
% 1.47/0.57  fof(f170,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2)) )),
% 1.47/0.57    inference(resolution,[],[f62,f33])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    v1_funct_1(sK5)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f616,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f615,f34])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    v1_funct_2(sK5,sK3,sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f615,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f614,f44])).
% 1.47/0.57  fof(f44,plain,(
% 1.47/0.57    ~v1_xboole_0(sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f614,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f613,f39])).
% 1.47/0.57  fof(f613,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),X0) = X2) )),
% 1.47/0.57    inference(resolution,[],[f595,f35])).
% 1.47/0.57  fof(f595,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X4))) | v1_xboole_0(X4) | ~v1_funct_2(sK5,X2,X4) | v1_xboole_0(X0) | k2_partfun1(X0,X4,X3,k9_subset_1(X1,X0,X2)) != k2_partfun1(X2,X4,sK5,k9_subset_1(X1,X0,X2)) | k2_partfun1(k4_subset_1(X1,X0,X2),X4,k1_tmap_1(X1,X4,X0,X2,X3,sK5),X0) = X3) )),
% 1.47/0.57    inference(resolution,[],[f343,f33])).
% 1.47/0.57  fof(f343,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X0) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f342,f74])).
% 1.47/0.57  fof(f74,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f65,f51])).
% 1.47/0.57  fof(f51,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f21])).
% 1.47/0.57  fof(f21,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.47/0.57  fof(f65,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f31])).
% 1.47/0.57  fof(f31,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f30])).
% 1.47/0.57  fof(f30,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f13])).
% 1.47/0.57  fof(f13,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.47/0.57  fof(f342,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f341,f75])).
% 1.47/0.57  fof(f75,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f64,f51])).
% 1.47/0.57  fof(f64,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f31])).
% 1.47/0.57  fof(f341,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f340,f51])).
% 1.47/0.57  fof(f340,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | v1_xboole_0(X2) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f339])).
% 1.47/0.57  fof(f339,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | v1_xboole_0(X2) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X1) = X4 | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(resolution,[],[f73,f76])).
% 1.47/0.57  fof(f76,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_xboole_0(X1)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f63,f51])).
% 1.47/0.57  fof(f63,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f31])).
% 1.47/0.57  fof(f73,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 1.47/0.57    inference(equality_resolution,[],[f47])).
% 1.47/0.57  fof(f47,plain,(
% 1.47/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.47/0.57    inference(cnf_transformation,[],[f19])).
% 1.47/0.57  fof(f19,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f18])).
% 1.47/0.57  fof(f18,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f12])).
% 1.47/0.57  fof(f12,axiom,(
% 1.47/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.47/0.57  fof(f551,plain,(
% 1.47/0.57    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    inference(subsumption_resolution,[],[f550,f38])).
% 1.47/0.57  fof(f550,plain,(
% 1.47/0.57    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    inference(subsumption_resolution,[],[f549,f37])).
% 1.47/0.57  fof(f549,plain,(
% 1.47/0.57    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    inference(subsumption_resolution,[],[f548,f36])).
% 1.47/0.57  fof(f548,plain,(
% 1.47/0.57    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    inference(subsumption_resolution,[],[f547,f113])).
% 1.47/0.57  fof(f547,plain,(
% 1.47/0.57    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    inference(superposition,[],[f546,f175])).
% 1.47/0.57  fof(f546,plain,(
% 1.47/0.57    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 1.47/0.57    inference(forward_demodulation,[],[f545,f92])).
% 1.47/0.57  fof(f545,plain,(
% 1.47/0.57    ( ! [X1] : (k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,X1,k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 1.47/0.57    inference(forward_demodulation,[],[f544,f167])).
% 1.47/0.57  fof(f544,plain,(
% 1.47/0.57    ( ! [X1] : (k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f542,f42])).
% 1.47/0.57  fof(f542,plain,(
% 1.47/0.57    ( ! [X1] : (k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | v1_xboole_0(sK2) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) )),
% 1.47/0.57    inference(resolution,[],[f540,f43])).
% 1.47/0.57  fof(f540,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)) )),
% 1.47/0.57    inference(resolution,[],[f539,f40])).
% 1.47/0.57  fof(f539,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X1,X0,sK3)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 1.47/0.57    inference(forward_demodulation,[],[f538,f172])).
% 1.47/0.57  fof(f538,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f537,f34])).
% 1.47/0.57  fof(f537,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f536,f44])).
% 1.47/0.57  fof(f536,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f535,f39])).
% 1.47/0.57  fof(f535,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X1)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(sK1) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(X0) | k2_partfun1(X0,sK1,X2,k9_subset_1(X1,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X1,X0,sK3)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,sK3),sK1,k1_tmap_1(X1,sK1,X0,sK3,X2,sK5),sK3)) )),
% 1.47/0.57    inference(resolution,[],[f503,f35])).
% 1.47/0.57  fof(f503,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X4))) | v1_xboole_0(X4) | ~v1_funct_2(sK5,X2,X4) | v1_xboole_0(X0) | k2_partfun1(X0,X4,X3,k9_subset_1(X1,X0,X2)) != k2_partfun1(X2,X4,sK5,k9_subset_1(X1,X0,X2)) | sK5 = k2_partfun1(k4_subset_1(X1,X0,X2),X4,k1_tmap_1(X1,X4,X0,X2,X3,sK5),X2)) )),
% 1.47/0.57    inference(resolution,[],[f206,f33])).
% 1.47/0.57  fof(f206,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X0) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f205,f74])).
% 1.47/0.57  fof(f205,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f204,f75])).
% 1.47/0.57  fof(f204,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f203,f51])).
% 1.47/0.57  fof(f203,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | v1_xboole_0(X2) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f202])).
% 1.47/0.57  fof(f202,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | k2_partfun1(X1,X0,X4,k9_subset_1(X2,X1,X3)) != k2_partfun1(X3,X0,X5,k9_subset_1(X2,X1,X3)) | v1_xboole_0(X2) | ~v1_funct_2(k1_tmap_1(X2,X0,X1,X3,X4,X5),k4_subset_1(X2,X1,X3),X0) | ~m1_subset_1(k1_tmap_1(X2,X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X2,X1,X3),X0))) | k2_partfun1(k4_subset_1(X2,X1,X3),X0,k1_tmap_1(X2,X0,X1,X3,X4,X5),X3) = X5 | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(resolution,[],[f72,f76])).
% 1.47/0.57  fof(f72,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | v1_xboole_0(X0) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 1.47/0.57    inference(equality_resolution,[],[f48])).
% 1.47/0.57  fof(f48,plain,(
% 1.47/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.47/0.57    inference(cnf_transformation,[],[f19])).
% 1.47/0.57  % (25429)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.57  fof(f177,plain,(
% 1.47/0.57    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.47/0.57    inference(subsumption_resolution,[],[f176,f113])).
% 1.47/0.57  fof(f176,plain,(
% 1.47/0.57    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.47/0.57    inference(backward_demodulation,[],[f174,f175])).
% 1.47/0.57  fof(f174,plain,(
% 1.47/0.57    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)),
% 1.47/0.57    inference(forward_demodulation,[],[f173,f92])).
% 1.47/0.57  fof(f173,plain,(
% 1.47/0.57    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    inference(backward_demodulation,[],[f169,f172])).
% 1.47/0.57  fof(f169,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    inference(backward_demodulation,[],[f32,f167])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  % (25427)Refutation not found, incomplete strategy% (25427)------------------------------
% 1.47/0.57  % (25427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (25427)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (25427)Memory used [KB]: 2174
% 1.47/0.57  % (25427)Time elapsed: 0.153 s
% 1.47/0.57  % (25427)------------------------------
% 1.47/0.57  % (25427)------------------------------
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (25411)------------------------------
% 1.47/0.57  % (25411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (25411)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (25411)Memory used [KB]: 7164
% 1.47/0.57  % (25411)Time elapsed: 0.118 s
% 1.47/0.57  % (25411)------------------------------
% 1.47/0.57  % (25411)------------------------------
% 1.47/0.58  % (25404)Success in time 0.215 s
%------------------------------------------------------------------------------

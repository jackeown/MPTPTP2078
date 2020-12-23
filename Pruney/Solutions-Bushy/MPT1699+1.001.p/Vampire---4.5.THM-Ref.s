%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1699+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:21 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  184 (13473 expanded)
%              Number of leaves         :    6 (2290 expanded)
%              Depth                    :   59
%              Number of atoms          : 1352 (140665 expanded)
%              Number of equality atoms :  144 (10424 expanded)
%              Maximal formula depth    :   27 (  10 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f557,plain,(
    $false ),
    inference(subsumption_resolution,[],[f556,f31])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
                          & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4))
                          & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                             => r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
                           => r1_funct_2(k4_subset_1(X0,X2,X3),X1,k4_subset_1(X0,X3,X2),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_tmap_1(X0,X1,X3,X2,X5,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tmap_1)).

fof(f556,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f555,f426])).

fof(f426,plain,(
    ~ r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(backward_demodulation,[],[f97,f425])).

fof(f425,plain,(
    k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) ),
    inference(forward_demodulation,[],[f424,f392])).

fof(f392,plain,(
    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f391,f371])).

fof(f371,plain,(
    m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    inference(forward_demodulation,[],[f370,f96])).

fof(f96,plain,(
    k4_subset_1(sK0,sK2,sK3) = k4_subset_1(sK0,sK3,sK2) ),
    inference(resolution,[],[f88,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK3,X1) = k4_subset_1(sK0,X1,sK3) ) ),
    inference(resolution,[],[f28,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f370,plain,(
    m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f369,f30])).

fof(f369,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f368,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f368,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK2),sK1))) ),
    inference(resolution,[],[f181,f28])).

fof(f181,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | m1_subset_1(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,sK3,sK2),sK1))) ) ),
    inference(subsumption_resolution,[],[f180,f26])).

fof(f26,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f180,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | m1_subset_1(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,sK3,sK2),sK1))) ) ),
    inference(subsumption_resolution,[],[f179,f24])).

fof(f24,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f179,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | m1_subset_1(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,sK3,sK2),sK1))) ) ),
    inference(subsumption_resolution,[],[f174,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f174,plain,(
    ! [X1] :
      ( v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | m1_subset_1(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,sK3,sK2),sK1))) ) ),
    inference(resolution,[],[f64,f25])).

fof(f25,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_funct_2(X8,X7,sK1)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X6)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK3,X7,sK5,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK3,X7),sK1))) ) ),
    inference(subsumption_resolution,[],[f63,f21])).

fof(f21,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK3,X7,sK5,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK3,X7),sK1))) ) ),
    inference(subsumption_resolution,[],[f62,f19])).

fof(f19,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X6)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK3,X7,sK5,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK3,X7),sK1))) ) ),
    inference(subsumption_resolution,[],[f61,f27])).

fof(f27,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X6,X8,X7] :
      ( v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X6)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK3,X7,sK5,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK3,X7),sK1))) ) ),
    inference(subsumption_resolution,[],[f51,f31])).

fof(f51,plain,(
    ! [X6,X8,X7] :
      ( v1_xboole_0(sK1)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X6)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK3,X7,sK5,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK3,X7),sK1))) ) ),
    inference(resolution,[],[f20,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,X2,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f20,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f391,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f390,f193])).

fof(f193,plain,(
    v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    inference(subsumption_resolution,[],[f192,f30])).

fof(f192,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    inference(subsumption_resolution,[],[f191,f32])).

fof(f191,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    inference(resolution,[],[f141,f28])).

fof(f141,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_funct_1(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(subsumption_resolution,[],[f140,f26])).

fof(f140,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_funct_1(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(subsumption_resolution,[],[f139,f24])).

fof(f139,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_funct_1(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(subsumption_resolution,[],[f134,f29])).

fof(f134,plain,(
    ! [X1] :
      ( v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_funct_1(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(resolution,[],[f56,f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X1,sK1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_funct_1(k1_tmap_1(X0,sK1,sK3,X1,sK5,X2)) ) ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_funct_1(k1_tmap_1(X0,sK1,sK3,X1,sK5,X2)) ) ),
    inference(subsumption_resolution,[],[f54,f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_funct_1(k1_tmap_1(X0,sK1,sK3,X1,sK5,X2)) ) ),
    inference(subsumption_resolution,[],[f53,f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_funct_1(k1_tmap_1(X0,sK1,sK3,X1,sK5,X2)) ) ),
    inference(subsumption_resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(sK1)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_funct_1(k1_tmap_1(X0,sK1,sK3,X1,sK5,X2)) ) ),
    inference(resolution,[],[f20,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,X2,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f390,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f389,f26])).

fof(f389,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f388,f25])).

fof(f388,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f387,f24])).

fof(f387,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f386,f21])).

fof(f386,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f385,f20])).

fof(f385,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f384,f19])).

fof(f384,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f383,f31])).

fof(f383,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(subsumption_resolution,[],[f382,f22])).

fof(f22,plain,(
    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f382,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3) ),
    inference(resolution,[],[f106,f286])).

fof(f286,plain,(
    v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(forward_demodulation,[],[f285,f96])).

fof(f285,plain,(
    v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1) ),
    inference(subsumption_resolution,[],[f284,f30])).

fof(f284,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1) ),
    inference(subsumption_resolution,[],[f283,f32])).

fof(f283,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK3,sK2),sK1) ),
    inference(resolution,[],[f161,f28])).

fof(f161,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_funct_2(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4),k4_subset_1(X1,sK3,sK2),sK1) ) ),
    inference(subsumption_resolution,[],[f160,f26])).

fof(f160,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_funct_2(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4),k4_subset_1(X1,sK3,sK2),sK1) ) ),
    inference(subsumption_resolution,[],[f159,f24])).

fof(f159,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_funct_2(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4),k4_subset_1(X1,sK3,sK2),sK1) ) ),
    inference(subsumption_resolution,[],[f154,f29])).

fof(f154,plain,(
    ! [X1] :
      ( v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | v1_funct_2(k1_tmap_1(X1,sK1,sK3,sK2,sK5,sK4),k4_subset_1(X1,sK3,sK2),sK1) ) ),
    inference(resolution,[],[f60,f25])).

fof(f60,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X5,X4,sK1)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK3,X4,sK5,X5),k4_subset_1(X3,sK3,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f59,f21])).

fof(f59,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK3,X4,sK5,X5),k4_subset_1(X3,sK3,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f58,f19])).

fof(f58,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK3,X4,sK5,X5),k4_subset_1(X3,sK3,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f57,f27])).

fof(f57,plain,(
    ! [X4,X5,X3] :
      ( v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK3,X4,sK5,X5),k4_subset_1(X3,sK3,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f50,f31])).

fof(f50,plain,(
    ! [X4,X5,X3] :
      ( v1_xboole_0(sK1)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK3,X4,sK5,X5),k4_subset_1(X3,sK3,X4),sK1) ) ),
    inference(resolution,[],[f20,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,X2,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | k2_partfun1(sK3,X0,X1,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,X0,X2,k9_subset_1(sK0,sK2,sK3))
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2))
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),sK3) = X1 ) ),
    inference(forward_demodulation,[],[f105,f89])).

fof(f89,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK2) = k9_subset_1(sK0,sK2,X0) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k2_partfun1(sK3,X0,X1,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X0,X2,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2))
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),sK3) = X1 ) ),
    inference(subsumption_resolution,[],[f104,f32])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k2_partfun1(sK3,X0,X1,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X0,X2,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),sK3) = X1 ) ),
    inference(subsumption_resolution,[],[f103,f30])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k2_partfun1(sK3,X0,X1,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X0,X2,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),sK3) = X1 ) ),
    inference(subsumption_resolution,[],[f102,f29])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k2_partfun1(sK3,X0,X1,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X0,X2,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),sK3) = X1 ) ),
    inference(subsumption_resolution,[],[f101,f28])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k2_partfun1(sK3,X0,X1,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X0,X2,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),sK3) = X1 ) ),
    inference(subsumption_resolution,[],[f98,f27])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,sK3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k2_partfun1(sK3,X0,X1,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X0,X2,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK3,sK2,X1,X2),sK3) = X1 ) ),
    inference(superposition,[],[f47,f96])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f424,plain,(
    k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f423,f22])).

fof(f423,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(forward_demodulation,[],[f422,f392])).

fof(f422,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f421,f21])).

fof(f421,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(forward_demodulation,[],[f420,f392])).

fof(f420,plain,
    ( ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f419,f20])).

fof(f419,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(forward_demodulation,[],[f418,f392])).

fof(f418,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f417,f19])).

fof(f417,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(forward_demodulation,[],[f416,f392])).

fof(f416,plain,
    ( ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f415,f371])).

fof(f415,plain,
    ( ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f414,f286])).

fof(f414,plain,
    ( ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f413,f193])).

fof(f413,plain,
    ( ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f412,f26])).

fof(f412,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f411,f32])).

fof(f411,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f410,f24])).

fof(f410,plain,
    ( ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f409,f28])).

fof(f409,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f408,f27])).

fof(f408,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f407,f30])).

fof(f407,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f406,f29])).

fof(f406,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f405,f31])).

fof(f405,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(subsumption_resolution,[],[f404,f25])).

fof(f404,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),sK3,sK1)
    | ~ m1_subset_1(k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3),k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4) = k1_tmap_1(sK0,sK1,sK2,sK3,sK4,k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK3)) ),
    inference(superposition,[],[f45,f403])).

fof(f403,plain,(
    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f402,f371])).

fof(f402,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f401,f193])).

fof(f401,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f400,f26])).

fof(f400,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f399,f25])).

fof(f399,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f398,f24])).

fof(f398,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f397,f21])).

fof(f397,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f396,f20])).

fof(f396,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f395,f19])).

fof(f395,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f394,f31])).

fof(f394,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(subsumption_resolution,[],[f393,f22])).

fof(f393,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
    | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),sK2) ),
    inference(resolution,[],[f112,f286])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k4_subset_1(sK0,sK2,sK3),X3)
      | k2_partfun1(sK3,X3,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,X3,X5,k9_subset_1(sK0,sK2,sK3))
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK3,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,sK2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))
      | ~ v1_funct_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5))
      | ~ m1_subset_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X3)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X3,k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),sK2) = X5 ) ),
    inference(forward_demodulation,[],[f111,f89])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k4_subset_1(sK0,sK2,sK3),X3)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK3,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,sK2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))
      | k2_partfun1(sK3,X3,X4,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X3,X5,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5))
      | ~ m1_subset_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X3)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X3,k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),sK2) = X5 ) ),
    inference(subsumption_resolution,[],[f110,f32])).

fof(f110,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k4_subset_1(sK0,sK2,sK3),X3)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK3,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,sK2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))
      | k2_partfun1(sK3,X3,X4,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X3,X5,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X3)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X3,k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),sK2) = X5 ) ),
    inference(subsumption_resolution,[],[f109,f30])).

fof(f109,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k4_subset_1(sK0,sK2,sK3),X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK3,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,sK2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))
      | k2_partfun1(sK3,X3,X4,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X3,X5,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X3)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X3,k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),sK2) = X5 ) ),
    inference(subsumption_resolution,[],[f108,f29])).

fof(f108,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k4_subset_1(sK0,sK2,sK3),X3)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK3,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,sK2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))
      | k2_partfun1(sK3,X3,X4,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X3,X5,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X3)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X3,k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),sK2) = X5 ) ),
    inference(subsumption_resolution,[],[f107,f28])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k4_subset_1(sK0,sK2,sK3),X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK3,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,sK2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))
      | k2_partfun1(sK3,X3,X4,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X3,X5,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X3)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X3,k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),sK2) = X5 ) ),
    inference(subsumption_resolution,[],[f99,f27])).

fof(f99,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k4_subset_1(sK0,sK2,sK3),X3)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK3,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X3)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,sK2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))
      | k2_partfun1(sK3,X3,X4,k9_subset_1(sK0,sK3,sK2)) != k2_partfun1(sK2,X3,X5,k9_subset_1(sK0,sK3,sK2))
      | ~ v1_funct_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X3)))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X3,k1_tmap_1(sK0,X3,sK3,sK2,X4,X5),sK2) = X5 ) ),
    inference(superposition,[],[f46,f96])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ v1_funct_2(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),X2,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),X3,X1)
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X2,X1,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3),k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k1_tmap_1(X0,X1,X2,X3,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3)) = X6 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),X2,X1)
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),k9_subset_1(X0,X2,X3))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
      | k1_tmap_1(X0,X1,X2,X3,k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2),X5) = X6 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
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
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,(
    ~ r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    inference(backward_demodulation,[],[f23,f96])).

fof(f23,plain,(
    ~ r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK3,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f555,plain,
    ( r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f554,f376])).

fof(f376,plain,(
    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    inference(subsumption_resolution,[],[f375,f30])).

fof(f375,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    inference(subsumption_resolution,[],[f374,f32])).

fof(f374,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    inference(resolution,[],[f187,f28])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) ) ),
    inference(subsumption_resolution,[],[f186,f21])).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) ) ),
    inference(subsumption_resolution,[],[f185,f19])).

fof(f185,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) ) ),
    inference(subsumption_resolution,[],[f182,f27])).

fof(f182,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) ) ),
    inference(resolution,[],[f83,f20])).

fof(f83,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_funct_2(X8,X7,sK1)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X6)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK2,X7,sK4,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK2,X7),sK1))) ) ),
    inference(subsumption_resolution,[],[f82,f26])).

fof(f82,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK2,X7,sK4,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK2,X7),sK1))) ) ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(X6)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK2,X7,sK4,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK2,X7),sK1))) ) ),
    inference(subsumption_resolution,[],[f80,f29])).

fof(f80,plain,(
    ! [X6,X8,X7] :
      ( v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(X6)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK2,X7,sK4,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK2,X7),sK1))) ) ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f70,plain,(
    ! [X6,X8,X7] :
      ( v1_xboole_0(sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X6))
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(X6)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,X7,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))
      | m1_subset_1(k1_tmap_1(X6,sK1,sK2,X7,sK4,X8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X6,sK2,X7),sK1))) ) ),
    inference(resolution,[],[f25,f37])).

fof(f554,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f465,f313])).

fof(f313,plain,(
    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f312,f30])).

fof(f312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f311,f32])).

fof(f311,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(resolution,[],[f167,f28])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f166,f21])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f165,f19])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) ) ),
    inference(subsumption_resolution,[],[f162,f27])).

fof(f162,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) ) ),
    inference(resolution,[],[f79,f20])).

fof(f79,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X5,X4,sK1)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK2,X4,sK4,X5),k4_subset_1(X3,sK2,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f78,f26])).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK2,X4,sK4,X5),k4_subset_1(X3,sK2,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f77,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK2,X4,sK4,X5),k4_subset_1(X3,sK2,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f76,f29])).

fof(f76,plain,(
    ! [X4,X5,X3] :
      ( v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK2,X4,sK4,X5),k4_subset_1(X3,sK2,X4),sK1) ) ),
    inference(subsumption_resolution,[],[f69,f31])).

fof(f69,plain,(
    ! [X4,X5,X3] :
      ( v1_xboole_0(sK1)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ v1_funct_1(sK4)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,sK2,X4,sK4,X5),k4_subset_1(X3,sK2,X4),sK1) ) ),
    inference(resolution,[],[f25,f36])).

fof(f465,plain,(
    ! [X15,X16] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X16,X15)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X16,X15)))
      | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,X16,X15,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
      | v1_xboole_0(X15) ) ),
    inference(forward_demodulation,[],[f464,f425])).

fof(f464,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X16,X15)))
      | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X16,X15)
      | v1_xboole_0(X15)
      | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,X16,X15,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(forward_demodulation,[],[f463,f425])).

fof(f463,plain,(
    ! [X15,X16] :
      ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X16,X15)
      | v1_xboole_0(X15)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(X16,X15)))
      | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,X16,X15,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(forward_demodulation,[],[f462,f425])).

fof(f462,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),X16,X15)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(X16,X15)))
      | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,X16,X15,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(subsumption_resolution,[],[f438,f376])).

fof(f438,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
      | v1_xboole_0(X15)
      | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),X16,X15)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(X16,X15)))
      | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,X16,X15,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(backward_demodulation,[],[f310,f425])).

fof(f310,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),X16,X15)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(X16,X15)))
      | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,X16,X15,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(subsumption_resolution,[],[f309,f31])).

fof(f309,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),X16,X15)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(X16,X15)))
      | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,X16,X15,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(subsumption_resolution,[],[f296,f193])).

fof(f296,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
      | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),X16,X15)
      | ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(X16,X15)))
      | r1_funct_2(k4_subset_1(sK0,sK2,sK3),sK1,X16,X15,k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4),k1_tmap_1(sK0,sK1,sK3,sK2,sK5,sK4)) ) ),
    inference(resolution,[],[f286,f48])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 != X5
      | r1_funct_2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

%------------------------------------------------------------------------------

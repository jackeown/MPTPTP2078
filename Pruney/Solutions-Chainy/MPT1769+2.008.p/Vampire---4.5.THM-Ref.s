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
% DateTime   : Thu Dec  3 13:18:45 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  104 (5537 expanded)
%              Number of leaves         :    8 (1056 expanded)
%              Depth                    :   20
%              Number of atoms          :  398 (91053 expanded)
%              Number of equality atoms :   33 (4336 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(global_subsumption,[],[f328,f327])).

fof(f327,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(backward_demodulation,[],[f281,f295])).

fof(f295,plain,(
    sK4 = sK6 ),
    inference(unit_resulting_resolution,[],[f212,f216,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f216,plain,(
    ! [X0] : r1_tarski(sK6,X0) ),
    inference(unit_resulting_resolution,[],[f205,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f57,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f205,plain,(
    v1_xboole_0(sK6) ),
    inference(global_subsumption,[],[f198,f197])).

fof(f197,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(backward_demodulation,[],[f145,f190])).

fof(f190,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f175,f157])).

fof(f157,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f40,f45,f46,f34,f43,f42,f41,f35,f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

fof(f35,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f175,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f34,f45,f46,f40,f40,f69,f43,f42,f41,f35,f36,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f69,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(backward_demodulation,[],[f38,f29])).

fof(f29,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f145,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(superposition,[],[f72,f138])).

fof(f138,plain,
    ( sK4 = sK6
    | v1_xboole_0(sK6) ),
    inference(resolution,[],[f134,f108])).

fof(f108,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK6) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f28,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f134,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK4 = sK6 ),
    inference(global_subsumption,[],[f36,f35,f34,f70,f71,f26,f133])).

fof(f133,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f62,f67])).

fof(f67,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) ),
    inference(backward_demodulation,[],[f30,f29])).

fof(f30,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 = X5
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f26,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f27,f29])).

fof(f27,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f25,f29])).

fof(f25,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f198,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(backward_demodulation,[],[f146,f190])).

fof(f146,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(superposition,[],[f73,f138])).

fof(f73,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f24,f29])).

fof(f24,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f212,plain,(
    ! [X0] : r1_tarski(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f204,f88])).

fof(f204,plain,(
    v1_xboole_0(sK4) ),
    inference(global_subsumption,[],[f200,f199])).

fof(f199,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(backward_demodulation,[],[f153,f190])).

fof(f153,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(superposition,[],[f72,f139])).

fof(f139,plain,
    ( sK4 = sK6
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f134,f107])).

fof(f107,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f52,f36])).

fof(f200,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(backward_demodulation,[],[f154,f190])).

fof(f154,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(superposition,[],[f73,f139])).

fof(f281,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(forward_demodulation,[],[f268,f247])).

fof(f247,plain,(
    sK4 = sK5 ),
    inference(unit_resulting_resolution,[],[f208,f212,f55])).

fof(f208,plain,(
    ! [X0] : r1_tarski(sK5,X0) ),
    inference(unit_resulting_resolution,[],[f203,f88])).

fof(f203,plain,(
    v1_xboole_0(sK5) ),
    inference(global_subsumption,[],[f202,f201])).

fof(f201,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(backward_demodulation,[],[f165,f190])).

fof(f165,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(superposition,[],[f72,f140])).

fof(f140,plain,
    ( sK4 = sK6
    | v1_xboole_0(sK5) ),
    inference(resolution,[],[f134,f106])).

fof(f106,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK5) ),
    inference(resolution,[],[f52,f33])).

fof(f33,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f202,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(backward_demodulation,[],[f166,f190])).

fof(f166,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(superposition,[],[f73,f140])).

fof(f268,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) ),
    inference(backward_demodulation,[],[f188,f247])).

fof(f188,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f72,f186])).

fof(f186,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_tmap_1(sK0,sK1,sK6,sK2) ),
    inference(forward_demodulation,[],[f177,f159])).

fof(f159,plain,(
    k2_tmap_1(sK0,sK1,sK6,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f40,f45,f46,f26,f43,f42,f41,f71,f70,f48])).

fof(f177,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f26,f45,f46,f40,f40,f69,f43,f42,f41,f71,f70,f47])).

fof(f328,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(backward_demodulation,[],[f280,f295])).

fof(f280,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(forward_demodulation,[],[f267,f247])).

fof(f267,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) ),
    inference(backward_demodulation,[],[f187,f247])).

fof(f187,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f73,f186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:57:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.33/0.54  % (10909)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.55  % (10912)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.56  % (10923)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.57/0.56  % (10917)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.57/0.57  % (10920)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.57/0.57  % (10917)Refutation not found, incomplete strategy% (10917)------------------------------
% 1.57/0.57  % (10917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (10911)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.57/0.57  % (10922)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.58  % (10913)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.57/0.58  % (10933)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.58  % (10910)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.57/0.59  % (10934)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.57/0.59  % (10932)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.57/0.59  % (10924)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.57/0.59  % (10917)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.59  
% 1.57/0.59  % (10917)Memory used [KB]: 10874
% 1.57/0.59  % (10917)Time elapsed: 0.148 s
% 1.57/0.59  % (10917)------------------------------
% 1.57/0.59  % (10917)------------------------------
% 1.57/0.59  % (10931)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.57/0.59  % (10927)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.59  % (10914)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.57/0.59  % (10916)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.57/0.60  % (10919)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.57/0.60  % (10915)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.57/0.60  % (10921)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.60  % (10935)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.60  % (10931)Refutation not found, incomplete strategy% (10931)------------------------------
% 1.57/0.60  % (10931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (10925)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.57/0.60  % (10926)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.57/0.60  % (10931)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.60  
% 1.57/0.60  % (10931)Memory used [KB]: 11001
% 1.57/0.60  % (10931)Time elapsed: 0.180 s
% 1.57/0.60  % (10931)------------------------------
% 1.57/0.60  % (10931)------------------------------
% 1.57/0.61  % (10938)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.61  % (10926)Refutation not found, incomplete strategy% (10926)------------------------------
% 1.57/0.61  % (10926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (10926)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.61  
% 1.57/0.61  % (10926)Memory used [KB]: 10746
% 1.57/0.61  % (10926)Time elapsed: 0.181 s
% 1.57/0.61  % (10926)------------------------------
% 1.57/0.61  % (10926)------------------------------
% 1.57/0.61  % (10918)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.61  % (10937)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.61  % (10928)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.57/0.62  % (10929)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.57/0.62  % (10936)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.62  % (10930)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.62  % (10933)Refutation found. Thanks to Tanya!
% 1.57/0.62  % SZS status Theorem for theBenchmark
% 1.57/0.62  % SZS output start Proof for theBenchmark
% 1.57/0.62  fof(f330,plain,(
% 1.57/0.62    $false),
% 1.57/0.62    inference(global_subsumption,[],[f328,f327])).
% 1.57/0.62  fof(f327,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f325])).
% 1.57/0.62  fof(f325,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 1.57/0.62    inference(backward_demodulation,[],[f281,f295])).
% 1.57/0.62  fof(f295,plain,(
% 1.57/0.62    sK4 = sK6),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f212,f216,f55])).
% 1.57/0.62  fof(f55,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.57/0.62    inference(cnf_transformation,[],[f3])).
% 1.57/0.62  fof(f3,axiom,(
% 1.57/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.57/0.62  fof(f216,plain,(
% 1.57/0.62    ( ! [X0] : (r1_tarski(sK6,X0)) )),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f205,f88])).
% 1.57/0.62  fof(f88,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.57/0.62    inference(resolution,[],[f57,f51])).
% 1.57/0.62  fof(f51,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f1])).
% 1.57/0.62  fof(f1,axiom,(
% 1.57/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.57/0.62  fof(f57,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f21])).
% 1.57/0.62  fof(f21,plain,(
% 1.57/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f2])).
% 1.57/0.62  fof(f2,axiom,(
% 1.57/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.62  fof(f205,plain,(
% 1.57/0.62    v1_xboole_0(sK6)),
% 1.57/0.62    inference(global_subsumption,[],[f198,f197])).
% 1.57/0.62  fof(f197,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f196])).
% 1.57/0.62  fof(f196,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 1.57/0.62    inference(backward_demodulation,[],[f145,f190])).
% 1.57/0.62  fof(f190,plain,(
% 1.57/0.62    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 1.57/0.62    inference(forward_demodulation,[],[f175,f157])).
% 1.57/0.62  fof(f157,plain,(
% 1.57/0.62    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f44,f40,f45,f46,f34,f43,f42,f41,f35,f36,f48])).
% 1.57/0.62  fof(f48,plain,(
% 1.57/0.62    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f17])).
% 1.57/0.62  fof(f17,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(flattening,[],[f16])).
% 1.57/0.62  fof(f16,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f7])).
% 1.57/0.62  fof(f7,axiom,(
% 1.57/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.57/0.62  fof(f36,plain,(
% 1.57/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f13,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.57/0.62    inference(flattening,[],[f12])).
% 1.57/0.62  fof(f12,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f11])).
% 1.57/0.62  fof(f11,negated_conjecture,(
% 1.57/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 1.57/0.62    inference(negated_conjecture,[],[f10])).
% 1.57/0.62  fof(f10,conjecture,(
% 1.57/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).
% 1.57/0.62  fof(f35,plain,(
% 1.57/0.62    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f41,plain,(
% 1.57/0.62    ~v2_struct_0(sK1)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f42,plain,(
% 1.57/0.62    v2_pre_topc(sK1)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f43,plain,(
% 1.57/0.62    l1_pre_topc(sK1)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f34,plain,(
% 1.57/0.62    v1_funct_1(sK4)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f46,plain,(
% 1.57/0.62    l1_pre_topc(sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f45,plain,(
% 1.57/0.62    v2_pre_topc(sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f40,plain,(
% 1.57/0.62    m1_pre_topc(sK2,sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f44,plain,(
% 1.57/0.62    ~v2_struct_0(sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f175,plain,(
% 1.57/0.62    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f44,f34,f45,f46,f40,f40,f69,f43,f42,f41,f35,f36,f47])).
% 1.57/0.62  fof(f47,plain,(
% 1.57/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | v2_struct_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f15])).
% 1.57/0.62  fof(f15,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(flattening,[],[f14])).
% 1.57/0.62  fof(f14,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f8])).
% 1.57/0.62  fof(f8,axiom,(
% 1.57/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.57/0.62  fof(f69,plain,(
% 1.57/0.62    m1_pre_topc(sK0,sK0)),
% 1.57/0.62    inference(backward_demodulation,[],[f38,f29])).
% 1.57/0.62  fof(f29,plain,(
% 1.57/0.62    sK0 = sK3),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f38,plain,(
% 1.57/0.62    m1_pre_topc(sK3,sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f145,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 1.57/0.62    inference(superposition,[],[f72,f138])).
% 1.57/0.62  fof(f138,plain,(
% 1.57/0.62    sK4 = sK6 | v1_xboole_0(sK6)),
% 1.57/0.62    inference(resolution,[],[f134,f108])).
% 1.57/0.62  fof(f108,plain,(
% 1.57/0.62    ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK6)),
% 1.57/0.62    inference(resolution,[],[f52,f70])).
% 1.57/0.62  fof(f70,plain,(
% 1.57/0.62    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.57/0.62    inference(forward_demodulation,[],[f28,f29])).
% 1.57/0.62  fof(f28,plain,(
% 1.57/0.62    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f52,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f20])).
% 1.57/0.62  fof(f20,plain,(
% 1.57/0.62    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.57/0.62    inference(ennf_transformation,[],[f5])).
% 1.57/0.62  fof(f5,axiom,(
% 1.57/0.62    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.57/0.62  fof(f134,plain,(
% 1.57/0.62    v1_xboole_0(u1_struct_0(sK1)) | sK4 = sK6),
% 1.57/0.62    inference(global_subsumption,[],[f36,f35,f34,f70,f71,f26,f133])).
% 1.57/0.62  fof(f133,plain,(
% 1.57/0.62    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f130])).
% 1.57/0.62  fof(f130,plain,(
% 1.57/0.62    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6 | v1_xboole_0(u1_struct_0(sK1))),
% 1.57/0.62    inference(resolution,[],[f62,f67])).
% 1.57/0.62  fof(f67,plain,(
% 1.57/0.62    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)),
% 1.57/0.62    inference(backward_demodulation,[],[f30,f29])).
% 1.57/0.62  fof(f30,plain,(
% 1.57/0.62    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f62,plain,(
% 1.57/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 = X5 | v1_xboole_0(X1)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f23])).
% 1.57/0.62  fof(f23,plain,(
% 1.57/0.62    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.57/0.62    inference(flattening,[],[f22])).
% 1.57/0.62  fof(f22,plain,(
% 1.57/0.62    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.57/0.62    inference(ennf_transformation,[],[f6])).
% 1.57/0.62  fof(f6,axiom,(
% 1.57/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.57/0.62  fof(f26,plain,(
% 1.57/0.62    v1_funct_1(sK6)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f71,plain,(
% 1.57/0.62    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.57/0.62    inference(forward_demodulation,[],[f27,f29])).
% 1.57/0.62  fof(f27,plain,(
% 1.57/0.62    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f72,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.57/0.62    inference(forward_demodulation,[],[f25,f29])).
% 1.57/0.62  fof(f25,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f198,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f195])).
% 1.57/0.62  fof(f195,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 1.57/0.62    inference(backward_demodulation,[],[f146,f190])).
% 1.57/0.62  fof(f146,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 1.57/0.62    inference(superposition,[],[f73,f138])).
% 1.57/0.62  fof(f73,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.57/0.62    inference(forward_demodulation,[],[f24,f29])).
% 1.57/0.62  fof(f24,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f212,plain,(
% 1.57/0.62    ( ! [X0] : (r1_tarski(sK4,X0)) )),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f204,f88])).
% 1.57/0.62  fof(f204,plain,(
% 1.57/0.62    v1_xboole_0(sK4)),
% 1.57/0.62    inference(global_subsumption,[],[f200,f199])).
% 1.57/0.62  fof(f199,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f194])).
% 1.57/0.62  fof(f194,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 1.57/0.62    inference(backward_demodulation,[],[f153,f190])).
% 1.57/0.62  fof(f153,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 1.57/0.62    inference(superposition,[],[f72,f139])).
% 1.57/0.62  fof(f139,plain,(
% 1.57/0.62    sK4 = sK6 | v1_xboole_0(sK4)),
% 1.57/0.62    inference(resolution,[],[f134,f107])).
% 1.57/0.62  fof(f107,plain,(
% 1.57/0.62    ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK4)),
% 1.57/0.62    inference(resolution,[],[f52,f36])).
% 1.57/0.62  fof(f200,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f193])).
% 1.57/0.62  fof(f193,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 1.57/0.62    inference(backward_demodulation,[],[f154,f190])).
% 1.57/0.62  fof(f154,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 1.57/0.62    inference(superposition,[],[f73,f139])).
% 1.57/0.62  fof(f281,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 1.57/0.62    inference(forward_demodulation,[],[f268,f247])).
% 1.57/0.62  fof(f247,plain,(
% 1.57/0.62    sK4 = sK5),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f208,f212,f55])).
% 1.57/0.62  fof(f208,plain,(
% 1.57/0.62    ( ! [X0] : (r1_tarski(sK5,X0)) )),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f203,f88])).
% 1.57/0.62  fof(f203,plain,(
% 1.57/0.62    v1_xboole_0(sK5)),
% 1.57/0.62    inference(global_subsumption,[],[f202,f201])).
% 1.57/0.62  fof(f201,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f192])).
% 1.57/0.62  fof(f192,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 1.57/0.62    inference(backward_demodulation,[],[f165,f190])).
% 1.57/0.62  fof(f165,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 1.57/0.62    inference(superposition,[],[f72,f140])).
% 1.57/0.62  fof(f140,plain,(
% 1.57/0.62    sK4 = sK6 | v1_xboole_0(sK5)),
% 1.57/0.62    inference(resolution,[],[f134,f106])).
% 1.57/0.62  fof(f106,plain,(
% 1.57/0.62    ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK5)),
% 1.57/0.62    inference(resolution,[],[f52,f33])).
% 1.57/0.62  fof(f33,plain,(
% 1.57/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.57/0.62    inference(cnf_transformation,[],[f13])).
% 1.57/0.62  fof(f202,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f191])).
% 1.57/0.62  fof(f191,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 1.57/0.62    inference(backward_demodulation,[],[f166,f190])).
% 1.57/0.62  fof(f166,plain,(
% 1.57/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 1.57/0.62    inference(superposition,[],[f73,f140])).
% 1.57/0.62  fof(f268,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)),
% 1.57/0.62    inference(backward_demodulation,[],[f188,f247])).
% 1.57/0.62  fof(f188,plain,(
% 1.57/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.57/0.62    inference(backward_demodulation,[],[f72,f186])).
% 1.57/0.62  fof(f186,plain,(
% 1.57/0.62    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_tmap_1(sK0,sK1,sK6,sK2)),
% 1.57/0.62    inference(forward_demodulation,[],[f177,f159])).
% 1.57/0.62  fof(f159,plain,(
% 1.57/0.62    k2_tmap_1(sK0,sK1,sK6,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2))),
% 1.57/0.62    inference(unit_resulting_resolution,[],[f44,f40,f45,f46,f26,f43,f42,f41,f71,f70,f48])).
% 1.57/0.63  fof(f177,plain,(
% 1.57/0.63    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2))),
% 1.57/0.63    inference(unit_resulting_resolution,[],[f44,f26,f45,f46,f40,f40,f69,f43,f42,f41,f71,f70,f47])).
% 1.57/0.63  fof(f328,plain,(
% 1.57/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 1.57/0.63    inference(duplicate_literal_removal,[],[f324])).
% 1.57/0.63  fof(f324,plain,(
% 1.57/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 1.57/0.63    inference(backward_demodulation,[],[f280,f295])).
% 1.57/0.63  fof(f280,plain,(
% 1.57/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK4) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 1.57/0.63    inference(forward_demodulation,[],[f267,f247])).
% 1.57/0.63  fof(f267,plain,(
% 1.57/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)),
% 1.57/0.63    inference(backward_demodulation,[],[f187,f247])).
% 1.57/0.63  fof(f187,plain,(
% 1.57/0.63    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.57/0.63    inference(backward_demodulation,[],[f73,f186])).
% 1.57/0.63  % SZS output end Proof for theBenchmark
% 1.57/0.63  % (10933)------------------------------
% 1.57/0.63  % (10933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.63  % (10933)Termination reason: Refutation
% 1.57/0.63  
% 1.57/0.63  % (10933)Memory used [KB]: 6524
% 1.57/0.63  % (10933)Time elapsed: 0.188 s
% 1.57/0.63  % (10933)------------------------------
% 1.57/0.63  % (10933)------------------------------
% 1.57/0.63  % (10908)Success in time 0.263 s
%------------------------------------------------------------------------------

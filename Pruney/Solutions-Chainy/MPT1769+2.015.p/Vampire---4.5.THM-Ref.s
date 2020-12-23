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
% DateTime   : Thu Dec  3 13:18:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 (11297 expanded)
%              Number of leaves         :   10 (2226 expanded)
%              Depth                    :   23
%              Number of atoms          :  441 (177183 expanded)
%              Number of equality atoms :   39 (8404 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(global_subsumption,[],[f545,f547])).

fof(f547,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(duplicate_literal_removal,[],[f546])).

fof(f546,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(forward_demodulation,[],[f537,f498])).

fof(f498,plain,(
    sK4 = sK5 ),
    inference(forward_demodulation,[],[f493,f304])).

fof(f304,plain,(
    ! [X0] : k2_xboole_0(sK5,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f280,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f280,plain,(
    ! [X0] : r1_tarski(sK5,X0) ),
    inference(unit_resulting_resolution,[],[f276,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f276,plain,(
    v1_xboole_0(sK5) ),
    inference(global_subsumption,[],[f275,f274])).

fof(f274,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(backward_demodulation,[],[f232,f263])).

fof(f263,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f248,f224])).

fof(f224,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f42,f47,f48,f36,f45,f44,f43,f37,f38,f50])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f37,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f248,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f36,f47,f48,f42,f42,f76,f45,f44,f43,f37,f38,f49])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f76,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(backward_demodulation,[],[f40,f31])).

fof(f31,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f232,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(superposition,[],[f79,f201])).

fof(f201,plain,
    ( sK4 = sK6
    | v1_xboole_0(sK5) ),
    inference(resolution,[],[f195,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK5) ),
    inference(resolution,[],[f115,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f107,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f98,f53])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f56,f82])).

fof(f82,plain,(
    r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f35,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f35,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f195,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK4 = sK6 ),
    inference(global_subsumption,[],[f38,f37,f36,f77,f78,f28,f194])).

fof(f194,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f69,f74])).

fof(f74,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) ),
    inference(backward_demodulation,[],[f32,f31])).

fof(f32,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f28,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f29,f31])).

fof(f29,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f30,f31])).

fof(f30,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f27,f31])).

fof(f27,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f275,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(backward_demodulation,[],[f233,f263])).

fof(f233,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK5) ),
    inference(superposition,[],[f80,f201])).

fof(f80,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f26,f31])).

fof(f26,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f493,plain,(
    sK5 = k2_xboole_0(sK5,sK4) ),
    inference(unit_resulting_resolution,[],[f282,f337,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP10(sK9(X0,X1,X2),X1,X0)
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f337,plain,(
    ! [X0] : ~ sP10(X0,sK4,sK5) ),
    inference(unit_resulting_resolution,[],[f282,f286,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ sP10(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f286,plain,(
    ! [X0] : ~ r2_hidden(X0,sK4) ),
    inference(unit_resulting_resolution,[],[f277,f53])).

fof(f277,plain,(
    v1_xboole_0(sK4) ),
    inference(global_subsumption,[],[f273,f272])).

fof(f272,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(backward_demodulation,[],[f217,f263])).

fof(f217,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(superposition,[],[f79,f199])).

fof(f199,plain,
    ( sK4 = sK6
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f195,f130])).

fof(f130,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f127,f52])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f125,f54])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f99,f53])).

fof(f99,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
      | ~ r2_hidden(X1,sK4) ) ),
    inference(resolution,[],[f56,f83])).

fof(f83,plain,(
    r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f38,f60])).

fof(f273,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(backward_demodulation,[],[f218,f263])).

fof(f218,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK4) ),
    inference(superposition,[],[f80,f199])).

fof(f282,plain,(
    ! [X0] : ~ r2_hidden(X0,sK5) ),
    inference(unit_resulting_resolution,[],[f276,f53])).

fof(f537,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK2),sK5) ),
    inference(backward_demodulation,[],[f447,f498])).

fof(f447,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f261,f415])).

fof(f415,plain,(
    sK5 = sK6 ),
    inference(forward_demodulation,[],[f411,f304])).

fof(f411,plain,(
    sK6 = k2_xboole_0(sK5,sK5) ),
    inference(unit_resulting_resolution,[],[f290,f312,f66])).

fof(f312,plain,(
    ! [X0] : ~ sP10(X0,sK5,sK5) ),
    inference(unit_resulting_resolution,[],[f282,f282,f63])).

fof(f290,plain,(
    ! [X0] : ~ r2_hidden(X0,sK6) ),
    inference(unit_resulting_resolution,[],[f278,f53])).

fof(f278,plain,(
    v1_xboole_0(sK6) ),
    inference(global_subsumption,[],[f271,f270])).

fof(f270,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(backward_demodulation,[],[f206,f263])).

fof(f206,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(superposition,[],[f79,f197])).

fof(f197,plain,
    ( sK4 = sK6
    | v1_xboole_0(sK6) ),
    inference(resolution,[],[f195,f135])).

fof(f135,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK6) ),
    inference(resolution,[],[f134,f52])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f132,f54])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f100,f53])).

fof(f100,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
      | ~ r2_hidden(X2,sK6) ) ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,(
    r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f77,f60])).

fof(f271,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(backward_demodulation,[],[f207,f263])).

fof(f207,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | v1_xboole_0(sK6) ),
    inference(superposition,[],[f80,f197])).

fof(f261,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f79,f259])).

fof(f259,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_tmap_1(sK0,sK1,sK6,sK2) ),
    inference(forward_demodulation,[],[f250,f226])).

fof(f226,plain,(
    k2_tmap_1(sK0,sK1,sK6,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f42,f47,f48,f28,f45,f44,f43,f78,f77,f50])).

fof(f250,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f28,f47,f48,f42,f42,f76,f45,f44,f43,f78,f77,f49])).

fof(f545,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(duplicate_literal_removal,[],[f544])).

fof(f544,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) ),
    inference(forward_demodulation,[],[f536,f498])).

fof(f536,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK2),sK5) ),
    inference(backward_demodulation,[],[f446,f498])).

fof(f446,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f260,f415])).

fof(f260,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f80,f259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:29:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (3001)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (3004)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (3005)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (3011)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (3009)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (3021)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (3022)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (3016)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3002)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (3026)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (3023)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (3027)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (3013)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (3006)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (3025)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (3015)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (3018)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (3017)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (3028)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (3024)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (3007)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (3020)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (3003)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (3019)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (3030)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (3010)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (3027)Refutation not found, incomplete strategy% (3027)------------------------------
% 0.21/0.56  % (3027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3012)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (3027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3027)Memory used [KB]: 10874
% 0.21/0.56  % (3027)Time elapsed: 0.111 s
% 0.21/0.56  % (3027)------------------------------
% 0.21/0.56  % (3027)------------------------------
% 0.21/0.56  % (3029)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (3014)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (3008)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (3023)Refutation not found, incomplete strategy% (3023)------------------------------
% 0.21/0.56  % (3023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3023)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3023)Memory used [KB]: 11001
% 0.21/0.56  % (3023)Time elapsed: 0.102 s
% 0.21/0.56  % (3023)------------------------------
% 0.21/0.56  % (3023)------------------------------
% 0.21/0.57  % (3018)Refutation not found, incomplete strategy% (3018)------------------------------
% 0.21/0.57  % (3018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (3018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (3018)Memory used [KB]: 10746
% 0.21/0.57  % (3018)Time elapsed: 0.163 s
% 0.21/0.57  % (3018)------------------------------
% 0.21/0.57  % (3018)------------------------------
% 0.21/0.59  % (3025)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f548,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(global_subsumption,[],[f545,f547])).
% 0.21/0.59  fof(f547,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f546])).
% 0.21/0.59  fof(f546,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 0.21/0.59    inference(forward_demodulation,[],[f537,f498])).
% 0.21/0.59  fof(f498,plain,(
% 0.21/0.59    sK4 = sK5),
% 0.21/0.59    inference(forward_demodulation,[],[f493,f304])).
% 0.21/0.59  fof(f304,plain,(
% 0.21/0.59    ( ! [X0] : (k2_xboole_0(sK5,X0) = X0) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f280,f55])).
% 0.21/0.59  fof(f55,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.59  fof(f280,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(sK5,X0)) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f276,f95])).
% 0.21/0.59  fof(f95,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.59    inference(resolution,[],[f57,f53])).
% 0.21/0.59  fof(f53,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.59  fof(f57,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.59  fof(f276,plain,(
% 0.21/0.59    v1_xboole_0(sK5)),
% 0.21/0.59    inference(global_subsumption,[],[f275,f274])).
% 0.21/0.59  fof(f274,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f265])).
% 0.21/0.59  fof(f265,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 0.21/0.59    inference(backward_demodulation,[],[f232,f263])).
% 0.21/0.59  fof(f263,plain,(
% 0.21/0.59    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 0.21/0.59    inference(forward_demodulation,[],[f248,f224])).
% 0.21/0.59  fof(f224,plain,(
% 0.21/0.59    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f46,f42,f47,f48,f36,f45,f44,f43,f37,f38,f50])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f18])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f17])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f13])).
% 0.21/0.59  fof(f13,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,negated_conjecture,(
% 0.21/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.21/0.59    inference(negated_conjecture,[],[f11])).
% 0.21/0.59  fof(f11,conjecture,(
% 0.21/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    ~v2_struct_0(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    v2_pre_topc(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    l1_pre_topc(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    v1_funct_1(sK4)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f48,plain,(
% 0.21/0.59    l1_pre_topc(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    v2_pre_topc(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    m1_pre_topc(sK2,sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ~v2_struct_0(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f248,plain,(
% 0.21/0.59    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f46,f36,f47,f48,f42,f42,f76,f45,f44,f43,f37,f38,f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | v2_struct_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f16])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.59    inference(flattening,[],[f15])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    m1_pre_topc(sK0,sK0)),
% 0.21/0.59    inference(backward_demodulation,[],[f40,f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    sK0 = sK3),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    m1_pre_topc(sK3,sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f232,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 0.21/0.59    inference(superposition,[],[f79,f201])).
% 0.21/0.59  fof(f201,plain,(
% 0.21/0.59    sK4 = sK6 | v1_xboole_0(sK5)),
% 0.21/0.59    inference(resolution,[],[f195,f116])).
% 0.21/0.59  fof(f116,plain,(
% 0.21/0.59    ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK5)),
% 0.21/0.59    inference(resolution,[],[f115,f52])).
% 0.21/0.59  fof(f52,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f115,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK5) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 0.21/0.59    inference(resolution,[],[f107,f54])).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.21/0.59  fof(f107,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) | ~r2_hidden(X0,sK5)) )),
% 0.21/0.59    inference(resolution,[],[f98,f53])).
% 0.21/0.59  fof(f98,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) | ~r2_hidden(X0,sK5)) )),
% 0.21/0.59    inference(resolution,[],[f56,f82])).
% 0.21/0.59  fof(f82,plain,(
% 0.21/0.59    r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f35,f60])).
% 0.21/0.59  fof(f60,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f56,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f23])).
% 0.21/0.59  fof(f195,plain,(
% 0.21/0.59    v1_xboole_0(u1_struct_0(sK1)) | sK4 = sK6),
% 0.21/0.59    inference(global_subsumption,[],[f38,f37,f36,f77,f78,f28,f194])).
% 0.21/0.59  fof(f194,plain,(
% 0.21/0.59    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.59  fof(f191,plain,(
% 0.21/0.59    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6 | v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.59    inference(resolution,[],[f69,f74])).
% 0.21/0.59  fof(f74,plain,(
% 0.21/0.59    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)),
% 0.21/0.59    inference(backward_demodulation,[],[f32,f31])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f69,plain,(
% 0.21/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 = X5 | v1_xboole_0(X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.21/0.59    inference(flattening,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    v1_funct_1(sK6)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.59    inference(forward_demodulation,[],[f29,f31])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f77,plain,(
% 0.21/0.59    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.59    inference(forward_demodulation,[],[f30,f31])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f79,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.21/0.59    inference(forward_demodulation,[],[f27,f31])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f275,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f264])).
% 0.21/0.59  fof(f264,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 0.21/0.59    inference(backward_demodulation,[],[f233,f263])).
% 0.21/0.59  fof(f233,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK5)),
% 0.21/0.59    inference(superposition,[],[f80,f201])).
% 0.21/0.59  fof(f80,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.21/0.59    inference(forward_demodulation,[],[f26,f31])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 0.21/0.59    inference(cnf_transformation,[],[f14])).
% 0.21/0.59  fof(f493,plain,(
% 0.21/0.59    sK5 = k2_xboole_0(sK5,sK4)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f282,f337,f66])).
% 0.21/0.59  fof(f66,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (sP10(sK9(X0,X1,X2),X1,X0) | r2_hidden(sK9(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.59    inference(cnf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.59  fof(f337,plain,(
% 0.21/0.59    ( ! [X0] : (~sP10(X0,sK4,sK5)) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f282,f286,f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X0,X3,X1] : (~sP10(X3,X1,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f3])).
% 0.21/0.59  fof(f286,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK4)) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f277,f53])).
% 0.21/0.59  fof(f277,plain,(
% 0.21/0.59    v1_xboole_0(sK4)),
% 0.21/0.59    inference(global_subsumption,[],[f273,f272])).
% 0.21/0.59  fof(f272,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f267])).
% 0.21/0.59  fof(f267,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 0.21/0.59    inference(backward_demodulation,[],[f217,f263])).
% 0.21/0.59  fof(f217,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 0.21/0.59    inference(superposition,[],[f79,f199])).
% 0.21/0.59  fof(f199,plain,(
% 0.21/0.59    sK4 = sK6 | v1_xboole_0(sK4)),
% 0.21/0.59    inference(resolution,[],[f195,f130])).
% 0.21/0.59  fof(f130,plain,(
% 0.21/0.59    ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK4)),
% 0.21/0.59    inference(resolution,[],[f127,f52])).
% 0.21/0.59  fof(f127,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK4) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 0.21/0.59    inference(resolution,[],[f125,f54])).
% 0.21/0.59  fof(f125,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~r2_hidden(X0,sK4)) )),
% 0.21/0.59    inference(resolution,[],[f99,f53])).
% 0.21/0.59  fof(f99,plain,(
% 0.21/0.59    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~r2_hidden(X1,sK4)) )),
% 0.21/0.59    inference(resolution,[],[f56,f83])).
% 0.21/0.59  fof(f83,plain,(
% 0.21/0.59    r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f38,f60])).
% 0.21/0.59  fof(f273,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f266])).
% 0.21/0.59  fof(f266,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 0.21/0.59    inference(backward_demodulation,[],[f218,f263])).
% 0.21/0.59  fof(f218,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK4)),
% 0.21/0.59    inference(superposition,[],[f80,f199])).
% 0.21/0.59  fof(f282,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK5)) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f276,f53])).
% 0.21/0.59  fof(f537,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK2),sK5)),
% 0.21/0.59    inference(backward_demodulation,[],[f447,f498])).
% 0.21/0.59  fof(f447,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.21/0.59    inference(backward_demodulation,[],[f261,f415])).
% 0.21/0.59  fof(f415,plain,(
% 0.21/0.59    sK5 = sK6),
% 0.21/0.59    inference(forward_demodulation,[],[f411,f304])).
% 0.21/0.59  fof(f411,plain,(
% 0.21/0.59    sK6 = k2_xboole_0(sK5,sK5)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f290,f312,f66])).
% 0.21/0.59  fof(f312,plain,(
% 0.21/0.59    ( ! [X0] : (~sP10(X0,sK5,sK5)) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f282,f282,f63])).
% 0.21/0.59  fof(f290,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK6)) )),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f278,f53])).
% 0.21/0.59  fof(f278,plain,(
% 0.21/0.59    v1_xboole_0(sK6)),
% 0.21/0.59    inference(global_subsumption,[],[f271,f270])).
% 0.21/0.59  fof(f270,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f269])).
% 0.21/0.59  fof(f269,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 0.21/0.59    inference(backward_demodulation,[],[f206,f263])).
% 0.21/0.59  fof(f206,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 0.21/0.59    inference(superposition,[],[f79,f197])).
% 0.21/0.59  fof(f197,plain,(
% 0.21/0.59    sK4 = sK6 | v1_xboole_0(sK6)),
% 0.21/0.59    inference(resolution,[],[f195,f135])).
% 0.21/0.59  fof(f135,plain,(
% 0.21/0.59    ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK6)),
% 0.21/0.59    inference(resolution,[],[f134,f52])).
% 0.21/0.59  fof(f134,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,sK6) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 0.21/0.59    inference(resolution,[],[f132,f54])).
% 0.21/0.59  fof(f132,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~r2_hidden(X0,sK6)) )),
% 0.21/0.59    inference(resolution,[],[f100,f53])).
% 0.21/0.59  fof(f100,plain,(
% 0.21/0.59    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~r2_hidden(X2,sK6)) )),
% 0.21/0.59    inference(resolution,[],[f56,f84])).
% 0.21/0.59  fof(f84,plain,(
% 0.21/0.59    r1_tarski(sK6,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f77,f60])).
% 0.21/0.59  fof(f271,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f268])).
% 0.21/0.59  fof(f268,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 0.21/0.59    inference(backward_demodulation,[],[f207,f263])).
% 0.21/0.59  fof(f207,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | v1_xboole_0(sK6)),
% 0.21/0.59    inference(superposition,[],[f80,f197])).
% 0.21/0.59  fof(f261,plain,(
% 0.21/0.59    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.21/0.59    inference(backward_demodulation,[],[f79,f259])).
% 0.21/0.59  fof(f259,plain,(
% 0.21/0.59    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_tmap_1(sK0,sK1,sK6,sK2)),
% 0.21/0.59    inference(forward_demodulation,[],[f250,f226])).
% 0.21/0.59  fof(f226,plain,(
% 0.21/0.59    k2_tmap_1(sK0,sK1,sK6,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f46,f42,f47,f48,f28,f45,f44,f43,f78,f77,f50])).
% 0.21/0.59  fof(f250,plain,(
% 0.21/0.59    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f46,f28,f47,f48,f42,f42,f76,f45,f44,f43,f78,f77,f49])).
% 0.21/0.59  fof(f545,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f544])).
% 0.21/0.59  fof(f544,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4)),
% 0.21/0.59    inference(forward_demodulation,[],[f536,f498])).
% 0.21/0.59  fof(f536,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK4) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK2),sK5)),
% 0.21/0.59    inference(backward_demodulation,[],[f446,f498])).
% 0.21/0.59  fof(f446,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.21/0.59    inference(backward_demodulation,[],[f260,f415])).
% 0.21/0.59  fof(f260,plain,(
% 0.21/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.21/0.59    inference(backward_demodulation,[],[f80,f259])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (3025)------------------------------
% 0.21/0.59  % (3025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (3025)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (3025)Memory used [KB]: 6652
% 0.21/0.59  % (3025)Time elapsed: 0.183 s
% 0.21/0.59  % (3025)------------------------------
% 0.21/0.59  % (3025)------------------------------
% 0.21/0.60  % (3000)Success in time 0.224 s
%------------------------------------------------------------------------------

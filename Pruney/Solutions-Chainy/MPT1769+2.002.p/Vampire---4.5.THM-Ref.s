%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:44 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  126 (1883 expanded)
%              Number of leaves         :   16 ( 372 expanded)
%              Depth                    :   13
%              Number of atoms          :  550 (29449 expanded)
%              Number of equality atoms :   34 (1362 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f606,plain,(
    $false ),
    inference(subsumption_resolution,[],[f604,f605])).

fof(f605,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(duplicate_literal_removal,[],[f576])).

fof(f576,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(backward_demodulation,[],[f279,f574])).

fof(f574,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f139,f267,f282,f281,f319,f328,f342,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f342,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f341,f274])).

fof(f274,plain,(
    sK4 = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(forward_demodulation,[],[f273,f126])).

fof(f126,plain,(
    sK4 = k7_relat_1(sK4,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f122,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f122,plain,(
    r1_tarski(k1_relat_1(sK4),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f119,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f119,plain,(
    v4_relat_1(sK4,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f116,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f61,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f273,plain,(
    k7_relat_1(sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(forward_demodulation,[],[f272,f136])).

fof(f136,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f59,f61,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f272,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f67,f102,f70,f71,f59,f68,f69,f66,f60,f61,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f60,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(backward_demodulation,[],[f63,f54])).

fof(f54,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f341,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)),k7_relat_1(sK4,u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f332,f278])).

fof(f278,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f271,f136])).

fof(f271,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f67,f65,f70,f71,f59,f68,f69,f66,f60,f61,f76])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f332,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(unit_resulting_resolution,[],[f69,f69,f70,f71,f59,f65,f102,f64,f65,f68,f67,f66,f60,f61,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f328,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f59,f65,f102,f68,f67,f66,f60,f61,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f319,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f59,f65,f102,f68,f67,f66,f60,f61,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f281,plain,(
    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f218,f278])).

fof(f218,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f111,f108,f107,f59,f60,f61,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f107,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f68,f72])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f108,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f71,f72])).

fof(f111,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f109,f72])).

fof(f109,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f65,f71,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f282,plain,(
    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f191,f278])).

fof(f191,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f111,f108,f107,f59,f60,f61,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f267,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f71,f67,f70,f59,f65,f69,f102,f68,f66,f60,f61,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f139,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(backward_demodulation,[],[f133,f136])).

fof(f133,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f59,f61,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f279,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(backward_demodulation,[],[f237,f278])).

fof(f237,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f106,f231])).

fof(f231,plain,(
    sK4 = sK6 ),
    inference(unit_resulting_resolution,[],[f59,f51,f112,f112,f104,f103,f100,f60,f61,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f100,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) ),
    inference(backward_demodulation,[],[f55,f54])).

fof(f55,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f53,f54])).

fof(f53,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f104,plain,(
    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f52,f54])).

fof(f52,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f112,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f66,f107,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f51,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f49,f54])).

fof(f49,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f604,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(duplicate_literal_removal,[],[f577])).

fof(f577,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(backward_demodulation,[],[f280,f574])).

fof(f280,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(backward_demodulation,[],[f236,f278])).

fof(f236,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f105,f231])).

fof(f105,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f50,f54])).

fof(f50,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (11465)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.45  % (11449)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % (11453)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.48  % (11447)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (11454)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (11445)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (11444)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (11463)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (11446)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (11452)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (11450)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (11461)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (11455)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (11462)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (11467)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (11460)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (11456)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (11459)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (11448)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (11451)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (11466)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (11458)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (11468)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (11457)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (11469)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.56  % (11464)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.99/0.62  % (11451)Refutation found. Thanks to Tanya!
% 1.99/0.62  % SZS status Theorem for theBenchmark
% 1.99/0.62  % SZS output start Proof for theBenchmark
% 1.99/0.62  fof(f606,plain,(
% 1.99/0.62    $false),
% 1.99/0.62    inference(subsumption_resolution,[],[f604,f605])).
% 1.99/0.62  fof(f605,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)),
% 1.99/0.62    inference(duplicate_literal_removal,[],[f576])).
% 1.99/0.62  fof(f576,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)),
% 1.99/0.62    inference(backward_demodulation,[],[f279,f574])).
% 1.99/0.62  fof(f574,plain,(
% 1.99/0.62    k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f139,f267,f282,f281,f319,f328,f342,f87])).
% 1.99/0.62  fof(f87,plain,(
% 1.99/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_funct_2(X0,X1,X2,X3)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f40])).
% 1.99/0.62  fof(f40,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.99/0.62    inference(flattening,[],[f39])).
% 1.99/0.62  fof(f39,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.99/0.62    inference(ennf_transformation,[],[f7])).
% 1.99/0.62  fof(f7,axiom,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.99/0.62  fof(f342,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k7_relat_1(sK4,u1_struct_0(sK2)))),
% 1.99/0.62    inference(forward_demodulation,[],[f341,f274])).
% 1.99/0.62  fof(f274,plain,(
% 1.99/0.62    sK4 = k2_tmap_1(sK0,sK1,sK4,sK0)),
% 1.99/0.62    inference(forward_demodulation,[],[f273,f126])).
% 1.99/0.62  fof(f126,plain,(
% 1.99/0.62    sK4 = k7_relat_1(sK4,u1_struct_0(sK0))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f116,f122,f78])).
% 1.99/0.62  fof(f78,plain,(
% 1.99/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.99/0.62    inference(cnf_transformation,[],[f33])).
% 1.99/0.62  fof(f33,plain,(
% 1.99/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.99/0.62    inference(flattening,[],[f32])).
% 1.99/0.62  fof(f32,plain,(
% 1.99/0.62    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/0.62    inference(ennf_transformation,[],[f2])).
% 1.99/0.62  fof(f2,axiom,(
% 1.99/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.99/0.62  fof(f122,plain,(
% 1.99/0.62    r1_tarski(k1_relat_1(sK4),u1_struct_0(sK0))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f116,f119,f80])).
% 1.99/0.62  fof(f80,plain,(
% 1.99/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f34])).
% 1.99/0.62  fof(f34,plain,(
% 1.99/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/0.62    inference(ennf_transformation,[],[f1])).
% 1.99/0.62  fof(f1,axiom,(
% 1.99/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.99/0.62  fof(f119,plain,(
% 1.99/0.62    v4_relat_1(sK4,u1_struct_0(sK0))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f61,f82])).
% 1.99/0.62  fof(f82,plain,(
% 1.99/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f36])).
% 1.99/0.62  fof(f36,plain,(
% 1.99/0.62    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.62    inference(ennf_transformation,[],[f19])).
% 1.99/0.62  fof(f19,plain,(
% 1.99/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.99/0.62    inference(pure_predicate_removal,[],[f4])).
% 1.99/0.62  fof(f4,axiom,(
% 1.99/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.99/0.62  fof(f61,plain,(
% 1.99/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f21,plain,(
% 1.99/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/0.62    inference(flattening,[],[f20])).
% 1.99/0.62  fof(f20,plain,(
% 1.99/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.99/0.62    inference(ennf_transformation,[],[f18])).
% 1.99/0.62  fof(f18,negated_conjecture,(
% 1.99/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 1.99/0.62    inference(negated_conjecture,[],[f17])).
% 1.99/0.62  fof(f17,conjecture,(
% 1.99/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).
% 1.99/0.62  fof(f116,plain,(
% 1.99/0.62    v1_relat_1(sK4)),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f61,f81])).
% 1.99/0.62  fof(f81,plain,(
% 1.99/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f35])).
% 1.99/0.62  fof(f35,plain,(
% 1.99/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.62    inference(ennf_transformation,[],[f3])).
% 1.99/0.62  fof(f3,axiom,(
% 1.99/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.99/0.62  fof(f273,plain,(
% 1.99/0.62    k7_relat_1(sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0)),
% 1.99/0.62    inference(forward_demodulation,[],[f272,f136])).
% 1.99/0.62  fof(f136,plain,(
% 1.99/0.62    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0) = k7_relat_1(sK4,X0)) )),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f59,f61,f88])).
% 1.99/0.62  fof(f88,plain,(
% 1.99/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f42])).
% 1.99/0.62  fof(f42,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.99/0.62    inference(flattening,[],[f41])).
% 1.99/0.62  fof(f41,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.99/0.62    inference(ennf_transformation,[],[f6])).
% 1.99/0.62  fof(f6,axiom,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.99/0.62  fof(f59,plain,(
% 1.99/0.62    v1_funct_1(sK4)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f272,plain,(
% 1.99/0.62    k2_tmap_1(sK0,sK1,sK4,sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f67,f102,f70,f71,f59,f68,f69,f66,f60,f61,f76])).
% 1.99/0.62  fof(f76,plain,(
% 1.99/0.62    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 1.99/0.62    inference(cnf_transformation,[],[f29])).
% 1.99/0.62  fof(f29,plain,(
% 1.99/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/0.62    inference(flattening,[],[f28])).
% 1.99/0.62  fof(f28,plain,(
% 1.99/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/0.62    inference(ennf_transformation,[],[f12])).
% 1.99/0.62  fof(f12,axiom,(
% 1.99/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.99/0.62  fof(f60,plain,(
% 1.99/0.62    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f66,plain,(
% 1.99/0.62    ~v2_struct_0(sK1)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f69,plain,(
% 1.99/0.62    ~v2_struct_0(sK0)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f68,plain,(
% 1.99/0.62    l1_pre_topc(sK1)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f71,plain,(
% 1.99/0.62    l1_pre_topc(sK0)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f70,plain,(
% 1.99/0.62    v2_pre_topc(sK0)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f102,plain,(
% 1.99/0.62    m1_pre_topc(sK0,sK0)),
% 1.99/0.62    inference(backward_demodulation,[],[f63,f54])).
% 1.99/0.62  fof(f54,plain,(
% 1.99/0.62    sK0 = sK3),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f63,plain,(
% 1.99/0.62    m1_pre_topc(sK3,sK0)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f67,plain,(
% 1.99/0.62    v2_pre_topc(sK1)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f341,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)),k7_relat_1(sK4,u1_struct_0(sK2)))),
% 1.99/0.62    inference(forward_demodulation,[],[f332,f278])).
% 1.99/0.62  fof(f278,plain,(
% 1.99/0.62    k2_tmap_1(sK0,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 1.99/0.62    inference(forward_demodulation,[],[f271,f136])).
% 1.99/0.62  fof(f271,plain,(
% 1.99/0.62    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f67,f65,f70,f71,f59,f68,f69,f66,f60,f61,f76])).
% 1.99/0.62  fof(f65,plain,(
% 1.99/0.62    m1_pre_topc(sK2,sK0)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f332,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k2_tmap_1(sK0,sK1,sK4,sK0)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f69,f69,f70,f71,f59,f65,f102,f64,f65,f68,f67,f66,f60,f61,f75])).
% 1.99/0.62  fof(f75,plain,(
% 1.99/0.62    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | v2_struct_0(X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f27])).
% 1.99/0.62  fof(f27,plain,(
% 1.99/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/0.62    inference(flattening,[],[f26])).
% 1.99/0.62  fof(f26,plain,(
% 1.99/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/0.62    inference(ennf_transformation,[],[f15])).
% 1.99/0.62  fof(f15,axiom,(
% 1.99/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).
% 1.99/0.62  fof(f64,plain,(
% 1.99/0.62    ~v2_struct_0(sK2)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f328,plain,(
% 1.99/0.62    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f69,f70,f71,f59,f65,f102,f68,f67,f66,f60,f61,f93])).
% 1.99/0.62  fof(f93,plain,(
% 1.99/0.62    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v2_struct_0(X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f46])).
% 1.99/0.62  fof(f46,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/0.62    inference(flattening,[],[f45])).
% 1.99/0.62  fof(f45,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/0.62    inference(ennf_transformation,[],[f14])).
% 1.99/0.62  fof(f14,axiom,(
% 1.99/0.62    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.99/0.62  fof(f319,plain,(
% 1.99/0.62    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f69,f70,f71,f59,f65,f102,f68,f67,f66,f60,f61,f92])).
% 1.99/0.62  fof(f92,plain,(
% 1.99/0.62    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v2_struct_0(X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f46])).
% 1.99/0.62  fof(f281,plain,(
% 1.99/0.62    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.99/0.62    inference(backward_demodulation,[],[f218,f278])).
% 1.99/0.62  fof(f218,plain,(
% 1.99/0.62    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f111,f108,f107,f59,f60,f61,f85])).
% 1.99/0.62  fof(f85,plain,(
% 1.99/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f38])).
% 1.99/0.62  fof(f38,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.99/0.62    inference(flattening,[],[f37])).
% 1.99/0.62  fof(f37,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.99/0.62    inference(ennf_transformation,[],[f13])).
% 1.99/0.62  fof(f13,axiom,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 1.99/0.62  fof(f107,plain,(
% 1.99/0.62    l1_struct_0(sK1)),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f68,f72])).
% 1.99/0.62  fof(f72,plain,(
% 1.99/0.62    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f22])).
% 1.99/0.62  fof(f22,plain,(
% 1.99/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.99/0.62    inference(ennf_transformation,[],[f8])).
% 1.99/0.62  fof(f8,axiom,(
% 1.99/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.99/0.62  fof(f108,plain,(
% 1.99/0.62    l1_struct_0(sK0)),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f71,f72])).
% 1.99/0.62  fof(f111,plain,(
% 1.99/0.62    l1_struct_0(sK2)),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f109,f72])).
% 1.99/0.62  fof(f109,plain,(
% 1.99/0.62    l1_pre_topc(sK2)),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f65,f71,f73])).
% 1.99/0.62  fof(f73,plain,(
% 1.99/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f23])).
% 1.99/0.62  fof(f23,plain,(
% 1.99/0.62    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.99/0.62    inference(ennf_transformation,[],[f9])).
% 1.99/0.62  fof(f9,axiom,(
% 1.99/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.99/0.62  fof(f282,plain,(
% 1.99/0.62    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.99/0.62    inference(backward_demodulation,[],[f191,f278])).
% 1.99/0.62  fof(f191,plain,(
% 1.99/0.62    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f111,f108,f107,f59,f60,f61,f84])).
% 1.99/0.62  fof(f84,plain,(
% 1.99/0.62    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f38])).
% 1.99/0.62  fof(f267,plain,(
% 1.99/0.62    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f71,f67,f70,f59,f65,f69,f102,f68,f66,f60,f61,f91])).
% 1.99/0.62  fof(f91,plain,(
% 1.99/0.62    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) )),
% 1.99/0.62    inference(cnf_transformation,[],[f46])).
% 1.99/0.62  fof(f139,plain,(
% 1.99/0.62    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 1.99/0.62    inference(backward_demodulation,[],[f133,f136])).
% 1.99/0.62  fof(f133,plain,(
% 1.99/0.62    ( ! [X0] : (v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0))) )),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f59,f61,f89])).
% 1.99/0.62  fof(f89,plain,(
% 1.99/0.62    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f44])).
% 1.99/0.62  fof(f44,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.99/0.62    inference(flattening,[],[f43])).
% 1.99/0.62  fof(f43,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.99/0.62    inference(ennf_transformation,[],[f5])).
% 1.99/0.62  fof(f5,axiom,(
% 1.99/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.99/0.62  fof(f279,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)),
% 1.99/0.62    inference(backward_demodulation,[],[f237,f278])).
% 1.99/0.62  fof(f237,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.99/0.62    inference(backward_demodulation,[],[f106,f231])).
% 1.99/0.62  fof(f231,plain,(
% 1.99/0.62    sK4 = sK6),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f59,f51,f112,f112,f104,f103,f100,f60,f61,f95])).
% 1.99/0.62  fof(f95,plain,(
% 1.99/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f48])).
% 1.99/0.62  fof(f48,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.99/0.62    inference(flattening,[],[f47])).
% 1.99/0.62  fof(f47,plain,(
% 1.99/0.62    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.99/0.62    inference(ennf_transformation,[],[f11])).
% 1.99/0.62  fof(f11,axiom,(
% 1.99/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.99/0.62  fof(f100,plain,(
% 1.99/0.62    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)),
% 1.99/0.62    inference(backward_demodulation,[],[f55,f54])).
% 1.99/0.62  fof(f55,plain,(
% 1.99/0.62    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f103,plain,(
% 1.99/0.62    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.99/0.62    inference(forward_demodulation,[],[f53,f54])).
% 1.99/0.62  fof(f53,plain,(
% 1.99/0.62    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f104,plain,(
% 1.99/0.62    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.99/0.62    inference(forward_demodulation,[],[f52,f54])).
% 1.99/0.62  fof(f52,plain,(
% 1.99/0.62    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f112,plain,(
% 1.99/0.62    ~v1_xboole_0(u1_struct_0(sK1))),
% 1.99/0.62    inference(unit_resulting_resolution,[],[f66,f107,f74])).
% 1.99/0.62  fof(f74,plain,(
% 1.99/0.62    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.62    inference(cnf_transformation,[],[f25])).
% 1.99/0.62  fof(f25,plain,(
% 1.99/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/0.62    inference(flattening,[],[f24])).
% 1.99/0.62  fof(f24,plain,(
% 1.99/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/0.62    inference(ennf_transformation,[],[f10])).
% 1.99/0.62  fof(f10,axiom,(
% 1.99/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.99/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.99/0.62  fof(f51,plain,(
% 1.99/0.62    v1_funct_1(sK6)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f106,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.99/0.62    inference(forward_demodulation,[],[f49,f54])).
% 1.99/0.62  fof(f49,plain,(
% 1.99/0.62    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  fof(f604,plain,(
% 1.99/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)),
% 1.99/0.62    inference(duplicate_literal_removal,[],[f577])).
% 1.99/0.62  fof(f577,plain,(
% 1.99/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)),
% 1.99/0.62    inference(backward_demodulation,[],[f280,f574])).
% 1.99/0.62  fof(f280,plain,(
% 1.99/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5)),
% 1.99/0.62    inference(backward_demodulation,[],[f236,f278])).
% 1.99/0.62  fof(f236,plain,(
% 1.99/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.99/0.62    inference(backward_demodulation,[],[f105,f231])).
% 1.99/0.62  fof(f105,plain,(
% 1.99/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.99/0.62    inference(forward_demodulation,[],[f50,f54])).
% 1.99/0.62  fof(f50,plain,(
% 1.99/0.62    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.99/0.62    inference(cnf_transformation,[],[f21])).
% 1.99/0.62  % SZS output end Proof for theBenchmark
% 1.99/0.62  % (11451)------------------------------
% 1.99/0.62  % (11451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.62  % (11451)Termination reason: Refutation
% 1.99/0.62  
% 1.99/0.62  % (11451)Memory used [KB]: 2302
% 1.99/0.62  % (11451)Time elapsed: 0.187 s
% 1.99/0.62  % (11451)------------------------------
% 1.99/0.62  % (11451)------------------------------
% 1.99/0.63  % (11443)Success in time 0.275 s
%------------------------------------------------------------------------------

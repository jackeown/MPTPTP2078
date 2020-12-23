%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:27 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 514 expanded)
%              Number of clauses        :  102 ( 120 expanded)
%              Number of leaves         :   27 ( 228 expanded)
%              Depth                    :   18
%              Number of atoms          : 1021 (7075 expanded)
%              Number of equality atoms :  185 (1023 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f37])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f16,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f39])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6)
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK5)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X3,X1,X4,X5)
                  & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X3,X1,sK4,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,X1,X4,X5)
                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK3,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,X1,X4,X5)
                          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,X1,X4,X5)
                        & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,sK1,X4,X5)
                            & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f51,f50,f49,f48,f47,f46,f45])).

fof(f85,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_969,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2453,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_2990,plain,
    ( X0 != u1_struct_0(X1)
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2453])).

cnf(c_5117,plain,
    ( k2_struct_0(X0) != u1_struct_0(X1)
    | k2_struct_0(X0) = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2990])).

cnf(c_7872,plain,
    ( k2_struct_0(X0) != u1_struct_0(X1)
    | k2_struct_0(X0) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_5117])).

cnf(c_9498,plain,
    ( k2_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k2_struct_0(X0) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_7872])).

cnf(c_13090,plain,
    ( k2_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k2_struct_0(sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_9498])).

cnf(c_3887,plain,
    ( k2_struct_0(X0) != u1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2990])).

cnf(c_5172,plain,
    ( k2_struct_0(X0) != u1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_3887])).

cnf(c_7118,plain,
    ( k2_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k2_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5172])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2061,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5842,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1914,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5636,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_1914])).

cnf(c_7,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4743,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2352,plain,
    ( X0 != X1
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_2909,plain,
    ( X0 != u1_struct_0(sK2)
    | u1_struct_0(sK2) = X0
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2352])).

cnf(c_4158,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2909])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1956,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | X1 = u1_struct_0(X0)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2576,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_4157,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2576])).

cnf(c_12,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_16,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_214,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_215,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_445,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | k2_struct_0(X2) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_215])).

cnf(c_446,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) != u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_541,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_542,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_546,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_29])).

cnf(c_547,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_590,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_547,c_18])).

cnf(c_612,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | k2_struct_0(X6) != u1_struct_0(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_446,c_590])).

cnf(c_613,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_struct_0(X3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_657,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_613,c_6,c_1])).

cnf(c_1888,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
    | r1_tmap_1(sK3,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(sK3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_2083,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),sK5)
    | r1_tmap_1(sK3,X1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(sK3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1888])).

cnf(c_3306,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(sK3) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1591,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_222,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_6])).

cnf(c_223,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_1574,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_2700,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1574])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2114,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

cnf(c_2115,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2114])).

cnf(c_3014,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2700,c_42,c_2115])).

cnf(c_3015,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3014])).

cnf(c_3022,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_3015])).

cnf(c_3023,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3022])).

cnf(c_974,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2835,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_974,c_26])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_410,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_2])).

cnf(c_2240,plain,
    ( ~ l1_pre_topc(sK3)
    | k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_968,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2170,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2112,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_30])).

cnf(c_970,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1919,plain,
    ( X0 != sK3
    | u1_struct_0(X0) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_2072,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1919])).

cnf(c_1887,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1588,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1643,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1588,c_23])).

cnf(c_1808,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1643])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1587,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1626,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1587,c_23])).

cnf(c_1800,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1626])).

cnf(c_997,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_983,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13090,c_7118,c_5842,c_5636,c_4743,c_4158,c_4157,c_3306,c_3023,c_2835,c_2240,c_2170,c_2114,c_2112,c_2072,c_1887,c_1808,c_1800,c_997,c_983,c_21,c_25,c_26,c_27,c_30,c_31,c_33,c_34,c_35,c_36,c_37,c_38,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.60/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.00  
% 3.60/1.00  ------  iProver source info
% 3.60/1.00  
% 3.60/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.00  git: non_committed_changes: false
% 3.60/1.00  git: last_make_outside_of_git: false
% 3.60/1.00  
% 3.60/1.00  ------ 
% 3.60/1.00  ------ Parsing...
% 3.60/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.00  ------ Proving...
% 3.60/1.00  ------ Problem Properties 
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  clauses                                 33
% 3.60/1.00  conjectures                             17
% 3.60/1.00  EPR                                     16
% 3.60/1.00  Horn                                    31
% 3.60/1.00  unary                                   17
% 3.60/1.00  binary                                  5
% 3.60/1.00  lits                                    94
% 3.60/1.00  lits eq                                 14
% 3.60/1.00  fd_pure                                 0
% 3.60/1.00  fd_pseudo                               0
% 3.60/1.00  fd_cond                                 0
% 3.60/1.00  fd_pseudo_cond                          2
% 3.60/1.00  AC symbols                              0
% 3.60/1.00  
% 3.60/1.00  ------ Input Options Time Limit: Unbounded
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  ------ 
% 3.60/1.00  Current options:
% 3.60/1.00  ------ 
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  ------ Proving...
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  % SZS status Theorem for theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  fof(f1,axiom,(
% 3.60/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f18,plain,(
% 3.60/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f1])).
% 3.60/1.00  
% 3.60/1.00  fof(f19,plain,(
% 3.60/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(flattening,[],[f18])).
% 3.60/1.00  
% 3.60/1.00  fof(f53,plain,(
% 3.60/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f19])).
% 3.60/1.00  
% 3.60/1.00  fof(f4,axiom,(
% 3.60/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f23,plain,(
% 3.60/1.00    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.60/1.00    inference(ennf_transformation,[],[f4])).
% 3.60/1.00  
% 3.60/1.00  fof(f56,plain,(
% 3.60/1.00    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.60/1.00    inference(cnf_transformation,[],[f23])).
% 3.60/1.00  
% 3.60/1.00  fof(f7,axiom,(
% 3.60/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f26,plain,(
% 3.60/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f7])).
% 3.60/1.00  
% 3.60/1.00  fof(f60,plain,(
% 3.60/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f26])).
% 3.60/1.00  
% 3.60/1.00  fof(f8,axiom,(
% 3.60/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f27,plain,(
% 3.60/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.60/1.00    inference(ennf_transformation,[],[f8])).
% 3.60/1.00  
% 3.60/1.00  fof(f61,plain,(
% 3.60/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.60/1.00    inference(cnf_transformation,[],[f27])).
% 3.60/1.00  
% 3.60/1.00  fof(f10,axiom,(
% 3.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f29,plain,(
% 3.60/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.60/1.00    inference(ennf_transformation,[],[f10])).
% 3.60/1.00  
% 3.60/1.00  fof(f30,plain,(
% 3.60/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.60/1.00    inference(flattening,[],[f29])).
% 3.60/1.00  
% 3.60/1.00  fof(f65,plain,(
% 3.60/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f30])).
% 3.60/1.00  
% 3.60/1.00  fof(f11,axiom,(
% 3.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f31,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.60/1.00    inference(ennf_transformation,[],[f11])).
% 3.60/1.00  
% 3.60/1.00  fof(f32,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.60/1.00    inference(flattening,[],[f31])).
% 3.60/1.00  
% 3.60/1.00  fof(f42,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.60/1.00    inference(nnf_transformation,[],[f32])).
% 3.60/1.00  
% 3.60/1.00  fof(f43,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.60/1.00    inference(flattening,[],[f42])).
% 3.60/1.00  
% 3.60/1.00  fof(f67,plain,(
% 3.60/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f43])).
% 3.60/1.00  
% 3.60/1.00  fof(f94,plain,(
% 3.60/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.60/1.00    inference(equality_resolution,[],[f67])).
% 3.60/1.00  
% 3.60/1.00  fof(f12,axiom,(
% 3.60/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f33,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f12])).
% 3.60/1.00  
% 3.60/1.00  fof(f69,plain,(
% 3.60/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f33])).
% 3.60/1.00  
% 3.60/1.00  fof(f15,axiom,(
% 3.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f37,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.60/1.00    inference(ennf_transformation,[],[f15])).
% 3.60/1.00  
% 3.60/1.00  fof(f38,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.60/1.00    inference(flattening,[],[f37])).
% 3.60/1.00  
% 3.60/1.00  fof(f44,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.60/1.00    inference(nnf_transformation,[],[f38])).
% 3.60/1.00  
% 3.60/1.00  fof(f73,plain,(
% 3.60/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f44])).
% 3.60/1.00  
% 3.60/1.00  fof(f96,plain,(
% 3.60/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.60/1.00    inference(equality_resolution,[],[f73])).
% 3.60/1.00  
% 3.60/1.00  fof(f16,conjecture,(
% 3.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f17,negated_conjecture,(
% 3.60/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.60/1.00    inference(negated_conjecture,[],[f16])).
% 3.60/1.00  
% 3.60/1.00  fof(f39,plain,(
% 3.60/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.60/1.00    inference(ennf_transformation,[],[f17])).
% 3.60/1.00  
% 3.60/1.00  fof(f40,plain,(
% 3.60/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.60/1.00    inference(flattening,[],[f39])).
% 3.60/1.00  
% 3.60/1.00  fof(f51,plain,(
% 3.60/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f50,plain,(
% 3.60/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f49,plain,(
% 3.60/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f48,plain,(
% 3.60/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f47,plain,(
% 3.60/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f46,plain,(
% 3.60/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f45,plain,(
% 3.60/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f52,plain,(
% 3.60/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f51,f50,f49,f48,f47,f46,f45])).
% 3.60/1.00  
% 3.60/1.00  fof(f85,plain,(
% 3.60/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f84,plain,(
% 3.60/1.00    v1_funct_1(sK4)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f14,axiom,(
% 3.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f35,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.60/1.00    inference(ennf_transformation,[],[f14])).
% 3.60/1.00  
% 3.60/1.00  fof(f36,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.60/1.00    inference(flattening,[],[f35])).
% 3.60/1.00  
% 3.60/1.00  fof(f71,plain,(
% 3.60/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f36])).
% 3.60/1.00  
% 3.60/1.00  fof(f6,axiom,(
% 3.60/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f25,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f6])).
% 3.60/1.00  
% 3.60/1.00  fof(f59,plain,(
% 3.60/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f25])).
% 3.60/1.00  
% 3.60/1.00  fof(f2,axiom,(
% 3.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f20,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.60/1.00    inference(ennf_transformation,[],[f2])).
% 3.60/1.00  
% 3.60/1.00  fof(f21,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.60/1.00    inference(flattening,[],[f20])).
% 3.60/1.00  
% 3.60/1.00  fof(f54,plain,(
% 3.60/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f21])).
% 3.60/1.00  
% 3.60/1.00  fof(f13,axiom,(
% 3.60/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f34,plain,(
% 3.60/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f13])).
% 3.60/1.00  
% 3.60/1.00  fof(f70,plain,(
% 3.60/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f34])).
% 3.60/1.00  
% 3.60/1.00  fof(f87,plain,(
% 3.60/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f9,axiom,(
% 3.60/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f28,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f9])).
% 3.60/1.00  
% 3.60/1.00  fof(f41,plain,(
% 3.60/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(nnf_transformation,[],[f28])).
% 3.60/1.00  
% 3.60/1.00  fof(f63,plain,(
% 3.60/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f41])).
% 3.60/1.00  
% 3.60/1.00  fof(f76,plain,(
% 3.60/1.00    l1_pre_topc(sK0)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f81,plain,(
% 3.60/1.00    m1_pre_topc(sK2,sK0)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f5,axiom,(
% 3.60/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f24,plain,(
% 3.60/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f5])).
% 3.60/1.00  
% 3.60/1.00  fof(f58,plain,(
% 3.60/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f24])).
% 3.60/1.00  
% 3.60/1.00  fof(f3,axiom,(
% 3.60/1.00    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f22,plain,(
% 3.60/1.00    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.60/1.00    inference(ennf_transformation,[],[f3])).
% 3.60/1.00  
% 3.60/1.00  fof(f55,plain,(
% 3.60/1.00    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f22])).
% 3.60/1.00  
% 3.60/1.00  fof(f83,plain,(
% 3.60/1.00    m1_pre_topc(sK3,sK0)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f91,plain,(
% 3.60/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f90,plain,(
% 3.60/1.00    sK5 = sK6),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f89,plain,(
% 3.60/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f92,plain,(
% 3.60/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f88,plain,(
% 3.60/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f86,plain,(
% 3.60/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f82,plain,(
% 3.60/1.00    ~v2_struct_0(sK3)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f80,plain,(
% 3.60/1.00    ~v2_struct_0(sK2)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f79,plain,(
% 3.60/1.00    l1_pre_topc(sK1)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f78,plain,(
% 3.60/1.00    v2_pre_topc(sK1)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f77,plain,(
% 3.60/1.00    ~v2_struct_0(sK1)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f75,plain,(
% 3.60/1.00    v2_pre_topc(sK0)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  fof(f74,plain,(
% 3.60/1.00    ~v2_struct_0(sK0)),
% 3.60/1.00    inference(cnf_transformation,[],[f52])).
% 3.60/1.00  
% 3.60/1.00  cnf(c_969,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2453,plain,
% 3.60/1.00      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_969]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2990,plain,
% 3.60/1.00      ( X0 != u1_struct_0(X1)
% 3.60/1.00      | X0 = u1_struct_0(X2)
% 3.60/1.00      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2453]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_5117,plain,
% 3.60/1.00      ( k2_struct_0(X0) != u1_struct_0(X1)
% 3.60/1.00      | k2_struct_0(X0) = u1_struct_0(X2)
% 3.60/1.00      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2990]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_7872,plain,
% 3.60/1.00      ( k2_struct_0(X0) != u1_struct_0(X1)
% 3.60/1.00      | k2_struct_0(X0) = u1_struct_0(sK2)
% 3.60/1.00      | u1_struct_0(sK2) != u1_struct_0(X1) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_5117]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_9498,plain,
% 3.60/1.00      ( k2_struct_0(X0) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.60/1.00      | k2_struct_0(X0) = u1_struct_0(sK2)
% 3.60/1.00      | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_7872]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_13090,plain,
% 3.60/1.00      ( k2_struct_0(sK3) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.60/1.00      | k2_struct_0(sK3) = u1_struct_0(sK2)
% 3.60/1.00      | u1_struct_0(sK2) != u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_9498]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_3887,plain,
% 3.60/1.00      ( k2_struct_0(X0) != u1_struct_0(X0)
% 3.60/1.00      | k2_struct_0(X0) = u1_struct_0(X1)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(X0) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2990]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_5172,plain,
% 3.60/1.00      ( k2_struct_0(X0) != u1_struct_0(X0)
% 3.60/1.00      | k2_struct_0(X0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.60/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(X0) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_3887]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_7118,plain,
% 3.60/1.00      ( k2_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.60/1.00      | k2_struct_0(sK3) != u1_struct_0(sK3)
% 3.60/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_5172]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_0,plain,
% 3.60/1.00      ( ~ l1_pre_topc(X0)
% 3.60/1.00      | ~ v1_pre_topc(X0)
% 3.60/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.60/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2061,plain,
% 3.60/1.00      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.60/1.00      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.60/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_5842,plain,
% 3.60/1.00      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.60/1.00      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.60/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2061]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_4,plain,
% 3.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.60/1.00      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.60/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1914,plain,
% 3.60/1.00      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.60/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_5636,plain,
% 3.60/1.00      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.60/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_1914]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_7,plain,
% 3.60/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.60/1.00      | ~ l1_pre_topc(X0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_4743,plain,
% 3.60/1.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.60/1.00      | ~ l1_pre_topc(sK2) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2352,plain,
% 3.60/1.00      ( X0 != X1 | u1_struct_0(sK2) != X1 | u1_struct_0(sK2) = X0 ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_969]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2909,plain,
% 3.60/1.00      ( X0 != u1_struct_0(sK2)
% 3.60/1.00      | u1_struct_0(sK2) = X0
% 3.60/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2352]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_4158,plain,
% 3.60/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != u1_struct_0(sK2)
% 3.60/1.00      | u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.60/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2909]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_9,plain,
% 3.60/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.60/1.00      | X2 = X1
% 3.60/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1956,plain,
% 3.60/1.00      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.60/1.00      | X1 = u1_struct_0(X0)
% 3.60/1.00      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2576,plain,
% 3.60/1.00      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.60/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.60/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_1956]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_4157,plain,
% 3.60/1.00      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.60/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.60/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2576]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_12,plain,
% 3.60/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.60/1.00      | ~ v2_pre_topc(X0)
% 3.60/1.00      | ~ l1_pre_topc(X0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_14,plain,
% 3.60/1.00      ( v1_tsep_1(X0,X1)
% 3.60/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.60/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.00      | ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_16,plain,
% 3.60/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.00      | ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_214,plain,
% 3.60/1.00      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.60/1.00      | v1_tsep_1(X0,X1)
% 3.60/1.00      | ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(global_propositional_subsumption,
% 3.60/1.00                [status(thm)],
% 3.60/1.00                [c_14,c_16]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_215,plain,
% 3.60/1.00      ( v1_tsep_1(X0,X1)
% 3.60/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.60/1.00      | ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(renaming,[status(thm)],[c_214]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_445,plain,
% 3.60/1.00      ( v1_tsep_1(X0,X1)
% 3.60/1.00      | ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | X1 != X2
% 3.60/1.00      | k2_struct_0(X2) != u1_struct_0(X0) ),
% 3.60/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_215]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_446,plain,
% 3.60/1.00      ( v1_tsep_1(X0,X1)
% 3.60/1.00      | ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | k2_struct_0(X1) != u1_struct_0(X0) ),
% 3.60/1.00      inference(unflattening,[status(thm)],[c_445]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_19,plain,
% 3.60/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.60/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.60/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.60/1.00      | ~ v1_tsep_1(X4,X0)
% 3.60/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_pre_topc(X0,X5)
% 3.60/1.00      | ~ m1_pre_topc(X4,X0)
% 3.60/1.00      | ~ m1_pre_topc(X4,X5)
% 3.60/1.00      | v2_struct_0(X5)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X4)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | ~ v1_funct_1(X2)
% 3.60/1.00      | ~ v2_pre_topc(X5)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X5)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_28,negated_conjecture,
% 3.60/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.60/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_541,plain,
% 3.60/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.60/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.60/1.00      | ~ v1_tsep_1(X4,X0)
% 3.60/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_pre_topc(X0,X5)
% 3.60/1.00      | ~ m1_pre_topc(X4,X0)
% 3.60/1.00      | ~ m1_pre_topc(X4,X5)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X5)
% 3.60/1.00      | v2_struct_0(X4)
% 3.60/1.00      | ~ v1_funct_1(X2)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X5)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X5)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.60/1.00      | sK4 != X2 ),
% 3.60/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_542,plain,
% 3.60/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.60/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.60/1.00      | ~ v1_tsep_1(X0,X3)
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_pre_topc(X3,X2)
% 3.60/1.00      | ~ m1_pre_topc(X0,X3)
% 3.60/1.00      | ~ m1_pre_topc(X0,X2)
% 3.60/1.00      | v2_struct_0(X3)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | ~ v1_funct_1(sK4)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(unflattening,[status(thm)],[c_541]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_29,negated_conjecture,
% 3.60/1.00      ( v1_funct_1(sK4) ),
% 3.60/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_546,plain,
% 3.60/1.00      ( v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X3)
% 3.60/1.00      | ~ m1_pre_topc(X0,X2)
% 3.60/1.00      | ~ m1_pre_topc(X0,X3)
% 3.60/1.00      | ~ m1_pre_topc(X3,X2)
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.60/1.00      | ~ v1_tsep_1(X0,X3)
% 3.60/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.60/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(global_propositional_subsumption,
% 3.60/1.00                [status(thm)],
% 3.60/1.00                [c_542,c_29]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_547,plain,
% 3.60/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.60/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.60/1.00      | ~ v1_tsep_1(X0,X3)
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_pre_topc(X3,X2)
% 3.60/1.00      | ~ m1_pre_topc(X0,X2)
% 3.60/1.00      | ~ m1_pre_topc(X0,X3)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X3)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(renaming,[status(thm)],[c_546]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_18,plain,
% 3.60/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ m1_pre_topc(X2,X0)
% 3.60/1.00      | m1_pre_topc(X2,X1)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_590,plain,
% 3.60/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.60/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.60/1.00      | ~ v1_tsep_1(X0,X3)
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_pre_topc(X3,X2)
% 3.60/1.00      | ~ m1_pre_topc(X0,X3)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X3)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(forward_subsumption_resolution,
% 3.60/1.00                [status(thm)],
% 3.60/1.00                [c_547,c_18]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_612,plain,
% 3.60/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.60/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_pre_topc(X5,X6)
% 3.60/1.00      | ~ m1_pre_topc(X0,X3)
% 3.60/1.00      | ~ m1_pre_topc(X3,X2)
% 3.60/1.00      | v2_struct_0(X3)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | ~ v2_pre_topc(X6)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X6)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | X0 != X5
% 3.60/1.00      | X3 != X6
% 3.60/1.00      | k2_struct_0(X6) != u1_struct_0(X5)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(resolution_lifted,[status(thm)],[c_446,c_590]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_613,plain,
% 3.60/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.60/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_pre_topc(X0,X3)
% 3.60/1.00      | ~ m1_pre_topc(X3,X2)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X3)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ v2_pre_topc(X3)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X3)
% 3.60/1.00      | k2_struct_0(X3) != u1_struct_0(X0)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(unflattening,[status(thm)],[c_612]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_6,plain,
% 3.60/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1,plain,
% 3.60/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | v2_pre_topc(X0)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_657,plain,
% 3.60/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.60/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_pre_topc(X3,X2)
% 3.60/1.00      | ~ m1_pre_topc(X0,X3)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X3)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | k2_struct_0(X3) != u1_struct_0(X0)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(forward_subsumption_resolution,
% 3.60/1.00                [status(thm)],
% 3.60/1.00                [c_613,c_6,c_1]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1888,plain,
% 3.60/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
% 3.60/1.00      | r1_tmap_1(sK3,X1,sK4,X3)
% 3.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_pre_topc(X0,sK3)
% 3.60/1.00      | ~ m1_pre_topc(sK3,X2)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | v2_struct_0(sK3)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | k2_struct_0(sK3) != u1_struct_0(X0)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_657]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2083,plain,
% 3.60/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),sK5)
% 3.60/1.00      | r1_tmap_1(sK3,X1,sK4,sK5)
% 3.60/1.00      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 3.60/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 3.60/1.00      | ~ m1_pre_topc(X0,sK3)
% 3.60/1.00      | ~ m1_pre_topc(sK3,X2)
% 3.60/1.00      | v2_struct_0(X0)
% 3.60/1.00      | v2_struct_0(X1)
% 3.60/1.00      | v2_struct_0(X2)
% 3.60/1.00      | v2_struct_0(sK3)
% 3.60/1.00      | ~ v2_pre_topc(X1)
% 3.60/1.00      | ~ v2_pre_topc(X2)
% 3.60/1.00      | ~ l1_pre_topc(X1)
% 3.60/1.00      | ~ l1_pre_topc(X2)
% 3.60/1.00      | k2_struct_0(sK3) != u1_struct_0(X0)
% 3.60/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_1888]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_3306,plain,
% 3.60/1.00      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 3.60/1.00      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.60/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.60/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.60/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.60/1.00      | ~ m1_pre_topc(sK2,sK3)
% 3.60/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.60/1.00      | v2_struct_0(sK0)
% 3.60/1.00      | v2_struct_0(sK2)
% 3.60/1.00      | v2_struct_0(sK1)
% 3.60/1.00      | v2_struct_0(sK3)
% 3.60/1.00      | ~ v2_pre_topc(sK0)
% 3.60/1.00      | ~ v2_pre_topc(sK1)
% 3.60/1.00      | ~ l1_pre_topc(sK0)
% 3.60/1.00      | ~ l1_pre_topc(sK1)
% 3.60/1.00      | k2_struct_0(sK3) != u1_struct_0(sK2)
% 3.60/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.60/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2083]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_17,plain,
% 3.60/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1591,plain,
% 3.60/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 3.60/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.60/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_26,negated_conjecture,
% 3.60/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.60/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_11,plain,
% 3.60/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.60/1.00      | ~ l1_pre_topc(X0)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_222,plain,
% 3.60/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.60/1.00      | ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(global_propositional_subsumption,
% 3.60/1.00                [status(thm)],
% 3.60/1.00                [c_11,c_6]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_223,plain,
% 3.60/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.60/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.60/1.00      | ~ l1_pre_topc(X1) ),
% 3.60/1.00      inference(renaming,[status(thm)],[c_222]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1574,plain,
% 3.60/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.60/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.60/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.60/1.00      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2700,plain,
% 3.60/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.60/1.00      | m1_pre_topc(X0,sK3) = iProver_top
% 3.60/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.60/1.00      inference(superposition,[status(thm)],[c_26,c_1574]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_37,negated_conjecture,
% 3.60/1.00      ( l1_pre_topc(sK0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_42,plain,
% 3.60/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.60/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_32,negated_conjecture,
% 3.60/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2114,plain,
% 3.60/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.60/1.00      inference(resolution,[status(thm)],[c_6,c_32]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2115,plain,
% 3.60/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.60/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.60/1.00      inference(predicate_to_equality,[status(thm)],[c_2114]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_3014,plain,
% 3.60/1.00      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.60/1.00      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.60/1.00      inference(global_propositional_subsumption,
% 3.60/1.00                [status(thm)],
% 3.60/1.00                [c_2700,c_42,c_2115]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_3015,plain,
% 3.60/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.60/1.00      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.60/1.00      inference(renaming,[status(thm)],[c_3014]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_3022,plain,
% 3.60/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.60/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.60/1.00      inference(superposition,[status(thm)],[c_1591,c_3015]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_3023,plain,
% 3.60/1.00      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 3.60/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3022]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_974,plain,
% 3.60/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 3.60/1.00      theory(equality) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2835,plain,
% 3.60/1.00      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.60/1.00      | ~ l1_pre_topc(sK3) ),
% 3.60/1.00      inference(resolution,[status(thm)],[c_974,c_26]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_5,plain,
% 3.60/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2,plain,
% 3.60/1.00      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_410,plain,
% 3.60/1.00      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.60/1.00      inference(resolution,[status(thm)],[c_5,c_2]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2240,plain,
% 3.60/1.00      ( ~ l1_pre_topc(sK3) | k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_410]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_968,plain,( X0 = X0 ),theory(equality) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2170,plain,
% 3.60/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_968]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_30,negated_conjecture,
% 3.60/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2112,plain,
% 3.60/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.60/1.00      inference(resolution,[status(thm)],[c_6,c_30]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_970,plain,
% 3.60/1.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.60/1.00      theory(equality) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1919,plain,
% 3.60/1.00      ( X0 != sK3 | u1_struct_0(X0) = u1_struct_0(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_970]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2072,plain,
% 3.60/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != sK3
% 3.60/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_1919]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1887,plain,
% 3.60/1.00      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_968]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_22,negated_conjecture,
% 3.60/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.60/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1588,plain,
% 3.60/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.60/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_23,negated_conjecture,
% 3.60/1.00      ( sK5 = sK6 ),
% 3.60/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1643,plain,
% 3.60/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.60/1.00      inference(light_normalisation,[status(thm)],[c_1588,c_23]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1808,plain,
% 3.60/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 3.60/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1643]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_24,negated_conjecture,
% 3.60/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.60/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1587,plain,
% 3.60/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.60/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1626,plain,
% 3.60/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.60/1.00      inference(light_normalisation,[status(thm)],[c_1587,c_23]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_1800,plain,
% 3.60/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 3.60/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1626]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_997,plain,
% 3.60/1.00      ( sK1 = sK1 ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_968]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_983,plain,
% 3.60/1.00      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_970]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_21,negated_conjecture,
% 3.60/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.60/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_25,negated_conjecture,
% 3.60/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.60/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_27,negated_conjecture,
% 3.60/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.60/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_31,negated_conjecture,
% 3.60/1.00      ( ~ v2_struct_0(sK3) ),
% 3.60/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_33,negated_conjecture,
% 3.60/1.00      ( ~ v2_struct_0(sK2) ),
% 3.60/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_34,negated_conjecture,
% 3.60/1.00      ( l1_pre_topc(sK1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_35,negated_conjecture,
% 3.60/1.00      ( v2_pre_topc(sK1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_36,negated_conjecture,
% 3.60/1.00      ( ~ v2_struct_0(sK1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_38,negated_conjecture,
% 3.60/1.00      ( v2_pre_topc(sK0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_39,negated_conjecture,
% 3.60/1.00      ( ~ v2_struct_0(sK0) ),
% 3.60/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(contradiction,plain,
% 3.60/1.00      ( $false ),
% 3.60/1.00      inference(minisat,
% 3.60/1.00                [status(thm)],
% 3.60/1.00                [c_13090,c_7118,c_5842,c_5636,c_4743,c_4158,c_4157,
% 3.60/1.00                 c_3306,c_3023,c_2835,c_2240,c_2170,c_2114,c_2112,c_2072,
% 3.60/1.00                 c_1887,c_1808,c_1800,c_997,c_983,c_21,c_25,c_26,c_27,
% 3.60/1.00                 c_30,c_31,c_33,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  ------                               Statistics
% 3.60/1.00  
% 3.60/1.00  ------ Selected
% 3.60/1.00  
% 3.60/1.00  total_time:                             0.449
% 3.60/1.00  
%------------------------------------------------------------------------------

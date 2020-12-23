%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:42 EST 2020

% Result     : Theorem 15.61s
% Output     : CNFRefutation 15.61s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 434 expanded)
%              Number of clauses        :   96 ( 106 expanded)
%              Number of leaves         :   19 ( 180 expanded)
%              Depth                    :   11
%              Number of atoms          : 1419 (9294 expanded)
%              Number of equality atoms :   65 (  72 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal clause size      :   50 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
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
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
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
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
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
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f23])).

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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X2)
                          & m1_pre_topc(X2,X3) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                             => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X2)
                            & m1_pre_topc(X2,X3) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ( m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) )
                               => ( m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,sK5),X4,X1)
          | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,sK5),u1_struct_0(X4),u1_struct_0(X1))
          | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,sK5)) )
        & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,sK5),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,sK5),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
              & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
              & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,X2)
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,sK4,X5),sK4,X1)
              | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,sK4,X5),u1_struct_0(sK4),u1_struct_0(X1))
              | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,sK4,X5)) )
            & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
            & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_pre_topc(sK4,X2)
        & m1_pre_topc(X2,X3)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                    | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                    | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                  & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                  & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X1,sK3,X4,X5),X4,X1)
                  | ~ v1_funct_2(k3_tmap_1(X0,X1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                  | ~ v1_funct_1(k3_tmap_1(X0,X1,sK3,X4,X5)) )
                & m1_subset_1(k3_tmap_1(X0,X1,sK3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v5_pre_topc(k3_tmap_1(X0,X1,sK3,X2,X5),X2,X1)
                & v1_funct_2(k3_tmap_1(X0,X1,sK3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(k3_tmap_1(X0,X1,sK3,X2,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,X2)
            & m1_pre_topc(X2,sK3)
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                      & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                      & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                      | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                    & m1_subset_1(k3_tmap_1(X0,X1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v5_pre_topc(k3_tmap_1(X0,X1,X3,sK2,X5),sK2,X1)
                    & v1_funct_2(k3_tmap_1(X0,X1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(k3_tmap_1(X0,X1,X3,sK2,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,sK2)
                & m1_pre_topc(sK2,X3)
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,sK1,X3,X4,X5),X4,sK1)
                          | ~ v1_funct_2(k3_tmap_1(X0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1))
                          | ~ v1_funct_1(k3_tmap_1(X0,sK1,X3,X4,X5)) )
                        & m1_subset_1(k3_tmap_1(X0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                        & v5_pre_topc(k3_tmap_1(X0,sK1,X3,X2,X5),X2,sK1)
                        & v1_funct_2(k3_tmap_1(X0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1))
                        & v1_funct_1(k3_tmap_1(X0,sK1,X3,X2,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1)
                              | ~ v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                              | ~ v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)) )
                            & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X2)
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                          ( ( ~ m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1)
                            | ~ v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1))
                            | ~ v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5)) )
                          & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1)
                          & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X2)
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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

fof(f40,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) )
    & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f32,f39,f38,f37,f36,f35,f34])).

fof(f63,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_481,plain,
    ( ~ v5_pre_topc(X0_50,X0_49,X1_49)
    | v5_pre_topc(X1_50,X0_49,X1_49)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_8350,plain,
    ( v5_pre_topc(X0_50,sK4,sK1)
    | ~ v5_pre_topc(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)),sK4,sK1)
    | X0_50 != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_35870,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v5_pre_topc(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)),sK4,sK1)
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8350])).

cnf(c_475,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1443,plain,
    ( X0_50 != X1_50
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != X1_50
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X0_50 ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_10431,plain,
    ( X0_50 != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X0_50
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_22661,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4))
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_10431])).

cnf(c_2552,plain,
    ( v5_pre_topc(X0_50,sK4,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4),sK4,sK1)
    | X0_50 != k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_4038,plain,
    ( v5_pre_topc(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)),sK4,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4),sK4,sK1)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) != k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_1814,plain,
    ( X0_50 != k3_tmap_1(sK0,sK1,sK3,sK4,sK5)
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X0_50
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_3821,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) != k3_tmap_1(sK0,sK1,sK3,sK4,sK5)
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1814])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_471,plain,
    ( ~ r2_funct_2(X0_51,X1_51,X0_50,X1_50)
    | ~ v1_funct_2(X1_50,X0_51,X1_51)
    | ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | X0_50 = X1_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3296,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k3_tmap_1(sK0,sK1,sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_13,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k3_tmap_1(X2,X1,X4,X3,X5)),k3_tmap_1(X2,X1,X4,X0,X5))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_459,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,k3_tmap_1(X2_49,X1_49,X4_49,X3_49,X0_50)),k3_tmap_1(X2_49,X1_49,X4_49,X0_49,X0_50))
    | ~ v1_funct_2(X0_50,u1_struct_0(X4_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X3_49,X4_49)
    | ~ m1_pre_topc(X4_49,X2_49)
    | ~ m1_pre_topc(X0_49,X3_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X3_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(X4_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1423,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK1),k3_tmap_1(X1_49,sK1,X2_49,X0_49,k3_tmap_1(X1_49,sK1,sK3,X2_49,sK5)),k3_tmap_1(X1_49,sK1,sK3,X0_49,sK5))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X2_49,X1_49)
    | ~ m1_pre_topc(X2_49,sK3)
    | ~ m1_pre_topc(sK3,X1_49)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_1694,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X1_49,X0_49,k3_tmap_1(sK0,sK1,sK3,X1_49,sK5)),k3_tmap_1(sK0,sK1,sK3,X0_49,sK5))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(X1_49,sK3)
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(X1_49,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_2109,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,X0_49,sK5))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK2)
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_2734,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2109])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_467,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X2_49,X0_49)
    | ~ m1_pre_topc(X0_49,X3_49)
    | ~ m1_pre_topc(X2_49,X3_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X3_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X3_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X3_49)
    | ~ v1_funct_1(X0_50)
    | k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k3_tmap_1(X3_49,X1_49,X0_49,X2_49,X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1408,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(X0_49,sK2)
    | ~ m1_pre_topc(sK2,X1_49)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X1_49)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_49)) = k3_tmap_1(X1_49,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_1668,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,X0_49)
    | ~ m1_pre_topc(sK4,X0_49)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k3_tmap_1(X0_49,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_2055,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1668])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_466,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | m1_subset_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1379,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(sK3,X1_49)
    | m1_subset_1(k3_tmap_1(X1_49,sK1,sK3,X0_49,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X1_49)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_1660,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0_49,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_2032,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_9,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_463,plain,
    ( ~ v5_pre_topc(X0_50,X0_49,X1_49)
    | v5_pre_topc(k2_tmap_1(X0_49,X1_49,X0_50,X2_49),X2_49,X1_49)
    | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X2_49,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X0_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X0_49)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1403,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_49),X0_49,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK2)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_1998,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_1374,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(sK2,X1_49)
    | m1_subset_1(k3_tmap_1(X1_49,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X1_49)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_1652,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1986,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_465,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v1_funct_2(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),u1_struct_0(X3_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1369,plain,
    ( v1_funct_2(k3_tmap_1(X0_49,sK1,sK3,X1_49,sK5),u1_struct_0(X1_49),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_49,X0_49)
    | ~ m1_pre_topc(sK3,X0_49)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_1639,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0_49,sK5),u1_struct_0(X0_49),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_1970,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_1364,plain,
    ( v1_funct_2(k3_tmap_1(X0_49,sK1,sK2,X1_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(X1_49),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_49,X0_49)
    | ~ m1_pre_topc(sK2,X0_49)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_1631,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(X0_49),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_1958,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_468,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X2_49,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X0_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X0_49)
    | ~ v1_funct_1(X0_50)
    | k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k2_tmap_1(X0_49,X1_49,X0_50,X2_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1354,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK2)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_49)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_49) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_1946,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_464,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1339,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(sK2,X1_49)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X1_49)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_49,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_1610,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_1928,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_443,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1166,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_470,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v2_pre_topc(X1_49)
    | v2_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1139,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_1759,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1139])).

cnf(c_1760,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1759])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_469,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1529,plain,
    ( ~ m1_pre_topc(sK2,X0_49)
    | ~ l1_pre_topc(X0_49)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_1740,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1344,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(sK3,X1_49)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X1_49)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_49,sK1,sK3,X0_49,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_1513,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0_49,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_1554,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1513])).

cnf(c_480,plain,
    ( X0_50 != X1_50
    | k3_tmap_1(X0_49,X1_49,X2_49,X3_49,X0_50) = k3_tmap_1(X0_49,X1_49,X2_49,X3_49,X1_50) ),
    theory(equality)).

cnf(c_1445,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK3,sK4,X0_50)
    | sK5 != X0_50 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1448,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK3,sK4,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_474,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_489,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_15,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35870,c_22661,c_4038,c_3821,c_3296,c_2734,c_2055,c_2032,c_1998,c_1986,c_1970,c_1958,c_1946,c_1928,c_1760,c_1740,c_1554,c_1448,c_489,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.61/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.61/2.50  
% 15.61/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.61/2.50  
% 15.61/2.50  ------  iProver source info
% 15.61/2.50  
% 15.61/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.61/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.61/2.50  git: non_committed_changes: false
% 15.61/2.50  git: last_make_outside_of_git: false
% 15.61/2.50  
% 15.61/2.50  ------ 
% 15.61/2.50  ------ Parsing...
% 15.61/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.61/2.50  
% 15.61/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.61/2.50  
% 15.61/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.61/2.50  
% 15.61/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.61/2.50  ------ Proving...
% 15.61/2.50  ------ Problem Properties 
% 15.61/2.50  
% 15.61/2.50  
% 15.61/2.50  clauses                                 37
% 15.61/2.50  conjectures                             22
% 15.61/2.50  EPR                                     19
% 15.61/2.50  Horn                                    28
% 15.61/2.50  unary                                   21
% 15.61/2.50  binary                                  1
% 15.61/2.50  lits                                    168
% 15.61/2.50  lits eq                                 3
% 15.61/2.50  fd_pure                                 0
% 15.61/2.50  fd_pseudo                               0
% 15.61/2.50  fd_cond                                 0
% 15.61/2.50  fd_pseudo_cond                          1
% 15.61/2.50  AC symbols                              0
% 15.61/2.50  
% 15.61/2.50  ------ Input Options Time Limit: Unbounded
% 15.61/2.50  
% 15.61/2.50  
% 15.61/2.50  ------ 
% 15.61/2.50  Current options:
% 15.61/2.50  ------ 
% 15.61/2.50  
% 15.61/2.50  
% 15.61/2.50  
% 15.61/2.50  
% 15.61/2.50  ------ Proving...
% 15.61/2.50  
% 15.61/2.50  
% 15.61/2.50  % SZS status Theorem for theBenchmark.p
% 15.61/2.50  
% 15.61/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.61/2.50  
% 15.61/2.50  fof(f1,axiom,(
% 15.61/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f13,plain,(
% 15.61/2.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.61/2.50    inference(ennf_transformation,[],[f1])).
% 15.61/2.50  
% 15.61/2.50  fof(f14,plain,(
% 15.61/2.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.61/2.50    inference(flattening,[],[f13])).
% 15.61/2.50  
% 15.61/2.50  fof(f33,plain,(
% 15.61/2.50    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.61/2.50    inference(nnf_transformation,[],[f14])).
% 15.61/2.50  
% 15.61/2.50  fof(f41,plain,(
% 15.61/2.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f33])).
% 15.61/2.50  
% 15.61/2.50  fof(f9,axiom,(
% 15.61/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f27,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.61/2.50    inference(ennf_transformation,[],[f9])).
% 15.61/2.50  
% 15.61/2.50  fof(f28,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.61/2.50    inference(flattening,[],[f27])).
% 15.61/2.50  
% 15.61/2.50  fof(f54,plain,(
% 15.61/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f28])).
% 15.61/2.50  
% 15.61/2.50  fof(f5,axiom,(
% 15.61/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f20,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.61/2.50    inference(ennf_transformation,[],[f5])).
% 15.61/2.50  
% 15.61/2.50  fof(f21,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.61/2.50    inference(flattening,[],[f20])).
% 15.61/2.50  
% 15.61/2.50  fof(f46,plain,(
% 15.61/2.50    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f21])).
% 15.61/2.50  
% 15.61/2.50  fof(f6,axiom,(
% 15.61/2.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f22,plain,(
% 15.61/2.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.61/2.50    inference(ennf_transformation,[],[f6])).
% 15.61/2.50  
% 15.61/2.50  fof(f23,plain,(
% 15.61/2.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.61/2.50    inference(flattening,[],[f22])).
% 15.61/2.50  
% 15.61/2.50  fof(f49,plain,(
% 15.61/2.50    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f23])).
% 15.61/2.50  
% 15.61/2.50  fof(f7,axiom,(
% 15.61/2.50    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f24,plain,(
% 15.61/2.50    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.61/2.50    inference(ennf_transformation,[],[f7])).
% 15.61/2.50  
% 15.61/2.50  fof(f25,plain,(
% 15.61/2.50    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.61/2.50    inference(flattening,[],[f24])).
% 15.61/2.50  
% 15.61/2.50  fof(f52,plain,(
% 15.61/2.50    ( ! [X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f25])).
% 15.61/2.50  
% 15.61/2.50  fof(f48,plain,(
% 15.61/2.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f23])).
% 15.61/2.50  
% 15.61/2.50  fof(f4,axiom,(
% 15.61/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f18,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.61/2.50    inference(ennf_transformation,[],[f4])).
% 15.61/2.50  
% 15.61/2.50  fof(f19,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.61/2.50    inference(flattening,[],[f18])).
% 15.61/2.50  
% 15.61/2.50  fof(f45,plain,(
% 15.61/2.50    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f19])).
% 15.61/2.50  
% 15.61/2.50  fof(f47,plain,(
% 15.61/2.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f23])).
% 15.61/2.50  
% 15.61/2.50  fof(f11,conjecture,(
% 15.61/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f12,negated_conjecture,(
% 15.61/2.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5))) => (m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5)))))))))))),
% 15.61/2.50    inference(negated_conjecture,[],[f11])).
% 15.61/2.50  
% 15.61/2.50  fof(f31,plain,(
% 15.61/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & (m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.61/2.50    inference(ennf_transformation,[],[f12])).
% 15.61/2.50  
% 15.61/2.50  fof(f32,plain,(
% 15.61/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.61/2.50    inference(flattening,[],[f31])).
% 15.61/2.50  
% 15.61/2.50  fof(f39,plain,(
% 15.61/2.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,sK5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,sK5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,sK5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,sK5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,sK5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 15.61/2.50    introduced(choice_axiom,[])).
% 15.61/2.50  
% 15.61/2.50  fof(f38,plain,(
% 15.61/2.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,sK4,X5),sK4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,sK4,X5),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,sK4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 15.61/2.50    introduced(choice_axiom,[])).
% 15.61/2.50  
% 15.61/2.50  fof(f37,plain,(
% 15.61/2.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,sK3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,sK3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,sK3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,sK3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,sK3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,sK3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,sK3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,sK3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 15.61/2.50    introduced(choice_axiom,[])).
% 15.61/2.50  
% 15.61/2.50  fof(f36,plain,(
% 15.61/2.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,sK2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,sK2,X5),sK2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,sK2,X5),u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,sK2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 15.61/2.50    introduced(choice_axiom,[])).
% 15.61/2.50  
% 15.61/2.50  fof(f35,plain,(
% 15.61/2.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,sK1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(X0,sK1,X3,X4,X5),X4,sK1) | ~v1_funct_2(k3_tmap_1(X0,sK1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(X0,sK1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,sK1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(X0,sK1,X3,X2,X5),X2,sK1) & v1_funct_2(k3_tmap_1(X0,sK1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(X0,sK1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 15.61/2.50    introduced(choice_axiom,[])).
% 15.61/2.50  
% 15.61/2.50  fof(f34,plain,(
% 15.61/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(X0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(X0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k3_tmap_1(sK0,X1,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,X3,X4,X5),X4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,X3,X4,X5))) & m1_subset_1(k3_tmap_1(sK0,X1,X3,X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK0,X1,X3,X2,X5),X2,X1) & v1_funct_2(k3_tmap_1(sK0,X1,X3,X2,X5),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 15.61/2.50    introduced(choice_axiom,[])).
% 15.61/2.50  
% 15.61/2.50  fof(f40,plain,(
% 15.61/2.50    ((((((~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))) & m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) & v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 15.61/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f32,f39,f38,f37,f36,f35,f34])).
% 15.61/2.50  
% 15.61/2.50  fof(f63,plain,(
% 15.61/2.50    m1_pre_topc(sK2,sK0)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f2,axiom,(
% 15.61/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f15,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.61/2.50    inference(ennf_transformation,[],[f2])).
% 15.61/2.50  
% 15.61/2.50  fof(f16,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.61/2.50    inference(flattening,[],[f15])).
% 15.61/2.50  
% 15.61/2.50  fof(f43,plain,(
% 15.61/2.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f16])).
% 15.61/2.50  
% 15.61/2.50  fof(f3,axiom,(
% 15.61/2.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.61/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.61/2.50  
% 15.61/2.50  fof(f17,plain,(
% 15.61/2.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.61/2.50    inference(ennf_transformation,[],[f3])).
% 15.61/2.50  
% 15.61/2.50  fof(f44,plain,(
% 15.61/2.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.61/2.50    inference(cnf_transformation,[],[f17])).
% 15.61/2.50  
% 15.61/2.50  fof(f77,plain,(
% 15.61/2.50    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f76,plain,(
% 15.61/2.50    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f75,plain,(
% 15.61/2.50    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f74,plain,(
% 15.61/2.50    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f73,plain,(
% 15.61/2.50    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f72,plain,(
% 15.61/2.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f71,plain,(
% 15.61/2.50    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f70,plain,(
% 15.61/2.50    v1_funct_1(sK5)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f69,plain,(
% 15.61/2.50    m1_pre_topc(sK4,sK2)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f68,plain,(
% 15.61/2.50    m1_pre_topc(sK2,sK3)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f67,plain,(
% 15.61/2.50    m1_pre_topc(sK4,sK0)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f66,plain,(
% 15.61/2.50    ~v2_struct_0(sK4)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f65,plain,(
% 15.61/2.50    m1_pre_topc(sK3,sK0)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f64,plain,(
% 15.61/2.50    ~v2_struct_0(sK3)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f62,plain,(
% 15.61/2.50    ~v2_struct_0(sK2)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f61,plain,(
% 15.61/2.50    l1_pre_topc(sK1)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f60,plain,(
% 15.61/2.50    v2_pre_topc(sK1)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f59,plain,(
% 15.61/2.50    ~v2_struct_0(sK1)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f58,plain,(
% 15.61/2.50    l1_pre_topc(sK0)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f57,plain,(
% 15.61/2.50    v2_pre_topc(sK0)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  fof(f56,plain,(
% 15.61/2.50    ~v2_struct_0(sK0)),
% 15.61/2.50    inference(cnf_transformation,[],[f40])).
% 15.61/2.50  
% 15.61/2.50  cnf(c_481,plain,
% 15.61/2.50      ( ~ v5_pre_topc(X0_50,X0_49,X1_49)
% 15.61/2.50      | v5_pre_topc(X1_50,X0_49,X1_49)
% 15.61/2.50      | X1_50 != X0_50 ),
% 15.61/2.50      theory(equality) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_8350,plain,
% 15.61/2.50      ( v5_pre_topc(X0_50,sK4,sK1)
% 15.61/2.50      | ~ v5_pre_topc(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)),sK4,sK1)
% 15.61/2.50      | X0_50 != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_481]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_35870,plain,
% 15.61/2.50      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
% 15.61/2.50      | ~ v5_pre_topc(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)),sK4,sK1)
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_8350]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_475,plain,
% 15.61/2.50      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 15.61/2.50      theory(equality) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1443,plain,
% 15.61/2.50      ( X0_50 != X1_50
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != X1_50
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X0_50 ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_475]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_10431,plain,
% 15.61/2.50      ( X0_50 != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X0_50
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1443]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_22661,plain,
% 15.61/2.50      ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4))
% 15.61/2.50      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_10431]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_2552,plain,
% 15.61/2.50      ( v5_pre_topc(X0_50,sK4,sK1)
% 15.61/2.50      | ~ v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4),sK4,sK1)
% 15.61/2.50      | X0_50 != k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_481]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_4038,plain,
% 15.61/2.50      ( v5_pre_topc(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)),sK4,sK1)
% 15.61/2.50      | ~ v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4),sK4,sK1)
% 15.61/2.50      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) != k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_2552]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1814,plain,
% 15.61/2.50      ( X0_50 != k3_tmap_1(sK0,sK1,sK3,sK4,sK5)
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X0_50
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK3,sK4,sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1443]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_3821,plain,
% 15.61/2.50      ( k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) != k3_tmap_1(sK0,sK1,sK3,sK4,sK5)
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK3,sK4,sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1814]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1,plain,
% 15.61/2.50      ( ~ r2_funct_2(X0,X1,X2,X3)
% 15.61/2.50      | ~ v1_funct_2(X3,X0,X1)
% 15.61/2.50      | ~ v1_funct_2(X2,X0,X1)
% 15.61/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.61/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.61/2.50      | ~ v1_funct_1(X3)
% 15.61/2.50      | ~ v1_funct_1(X2)
% 15.61/2.50      | X2 = X3 ),
% 15.61/2.50      inference(cnf_transformation,[],[f41]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_471,plain,
% 15.61/2.50      ( ~ r2_funct_2(X0_51,X1_51,X0_50,X1_50)
% 15.61/2.50      | ~ v1_funct_2(X1_50,X0_51,X1_51)
% 15.61/2.50      | ~ v1_funct_2(X0_50,X0_51,X1_51)
% 15.61/2.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 15.61/2.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 15.61/2.50      | ~ v1_funct_1(X0_50)
% 15.61/2.50      | ~ v1_funct_1(X1_50)
% 15.61/2.50      | X0_50 = X1_50 ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_1]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_3296,plain,
% 15.61/2.50      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
% 15.61/2.50      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
% 15.61/2.50      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
% 15.61/2.50      | k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) = k3_tmap_1(sK0,sK1,sK3,sK4,sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_471]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_13,plain,
% 15.61/2.50      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k3_tmap_1(X2,X1,X4,X3,X5)),k3_tmap_1(X2,X1,X4,X0,X5))
% 15.61/2.50      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
% 15.61/2.50      | ~ m1_pre_topc(X3,X2)
% 15.61/2.50      | ~ m1_pre_topc(X3,X4)
% 15.61/2.50      | ~ m1_pre_topc(X4,X2)
% 15.61/2.50      | ~ m1_pre_topc(X0,X3)
% 15.61/2.50      | ~ m1_pre_topc(X0,X2)
% 15.61/2.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
% 15.61/2.50      | v2_struct_0(X2)
% 15.61/2.50      | v2_struct_0(X1)
% 15.61/2.50      | v2_struct_0(X3)
% 15.61/2.50      | v2_struct_0(X0)
% 15.61/2.50      | v2_struct_0(X4)
% 15.61/2.50      | ~ l1_pre_topc(X2)
% 15.61/2.50      | ~ l1_pre_topc(X1)
% 15.61/2.50      | ~ v2_pre_topc(X2)
% 15.61/2.50      | ~ v2_pre_topc(X1)
% 15.61/2.50      | ~ v1_funct_1(X5) ),
% 15.61/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_459,plain,
% 15.61/2.50      ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,k3_tmap_1(X2_49,X1_49,X4_49,X3_49,X0_50)),k3_tmap_1(X2_49,X1_49,X4_49,X0_49,X0_50))
% 15.61/2.50      | ~ v1_funct_2(X0_50,u1_struct_0(X4_49),u1_struct_0(X1_49))
% 15.61/2.50      | ~ m1_pre_topc(X3_49,X2_49)
% 15.61/2.50      | ~ m1_pre_topc(X3_49,X4_49)
% 15.61/2.50      | ~ m1_pre_topc(X4_49,X2_49)
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X3_49)
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X2_49)
% 15.61/2.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_49),u1_struct_0(X1_49))))
% 15.61/2.50      | v2_struct_0(X2_49)
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(X3_49)
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | v2_struct_0(X4_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X2_49)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(X2_49)
% 15.61/2.50      | ~ v1_funct_1(X0_50) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_13]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1423,plain,
% 15.61/2.50      ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK1),k3_tmap_1(X1_49,sK1,X2_49,X0_49,k3_tmap_1(X1_49,sK1,sK3,X2_49,sK5)),k3_tmap_1(X1_49,sK1,sK3,X0_49,sK5))
% 15.61/2.50      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X2_49)
% 15.61/2.50      | ~ m1_pre_topc(X2_49,X1_49)
% 15.61/2.50      | ~ m1_pre_topc(X2_49,sK3)
% 15.61/2.50      | ~ m1_pre_topc(sK3,X1_49)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X2_49)
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | v2_struct_0(sK3)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_459]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1694,plain,
% 15.61/2.50      ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X1_49,X0_49,k3_tmap_1(sK0,sK1,sK3,X1_49,sK5)),k3_tmap_1(sK0,sK1,sK3,X0_49,sK5))
% 15.61/2.50      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ m1_pre_topc(X1_49,sK3)
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(X1_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | v2_struct_0(sK3)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1423]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_2109,plain,
% 15.61/2.50      ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,X0_49,sK5))
% 15.61/2.50      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK2)
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK3)
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | v2_struct_0(sK2)
% 15.61/2.50      | v2_struct_0(sK3)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1694]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_2734,plain,
% 15.61/2.50      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
% 15.61/2.50      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK3)
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK2)
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK2)
% 15.61/2.50      | v2_struct_0(sK4)
% 15.61/2.50      | v2_struct_0(sK3)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_2109]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_5,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.61/2.50      | ~ m1_pre_topc(X3,X4)
% 15.61/2.50      | ~ m1_pre_topc(X3,X1)
% 15.61/2.50      | ~ m1_pre_topc(X1,X4)
% 15.61/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.61/2.50      | v2_struct_0(X4)
% 15.61/2.50      | v2_struct_0(X2)
% 15.61/2.50      | ~ l1_pre_topc(X4)
% 15.61/2.50      | ~ l1_pre_topc(X2)
% 15.61/2.50      | ~ v2_pre_topc(X4)
% 15.61/2.50      | ~ v2_pre_topc(X2)
% 15.61/2.50      | ~ v1_funct_1(X0)
% 15.61/2.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f46]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_467,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 15.61/2.50      | ~ m1_pre_topc(X2_49,X0_49)
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X3_49)
% 15.61/2.50      | ~ m1_pre_topc(X2_49,X3_49)
% 15.61/2.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(X3_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X3_49)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(X3_49)
% 15.61/2.50      | ~ v1_funct_1(X0_50)
% 15.61/2.50      | k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k3_tmap_1(X3_49,X1_49,X0_49,X2_49,X0_50) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_5]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1408,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK2)
% 15.61/2.50      | ~ m1_pre_topc(sK2,X1_49)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 15.61/2.50      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_49)) = k3_tmap_1(X1_49,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_467]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1668,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK2,X0_49)
% 15.61/2.50      | ~ m1_pre_topc(sK4,X0_49)
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK2)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X0_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X0_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 15.61/2.50      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k3_tmap_1(X0_49,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1408]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_2055,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK2)
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK0)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 15.61/2.50      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1668]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_6,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.61/2.50      | ~ m1_pre_topc(X3,X4)
% 15.61/2.50      | ~ m1_pre_topc(X1,X4)
% 15.61/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.61/2.50      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 15.61/2.50      | v2_struct_0(X4)
% 15.61/2.50      | v2_struct_0(X2)
% 15.61/2.50      | ~ l1_pre_topc(X4)
% 15.61/2.50      | ~ l1_pre_topc(X2)
% 15.61/2.50      | ~ v2_pre_topc(X4)
% 15.61/2.50      | ~ v2_pre_topc(X2)
% 15.61/2.50      | ~ v1_funct_1(X0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_466,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X2_49)
% 15.61/2.50      | ~ m1_pre_topc(X3_49,X2_49)
% 15.61/2.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 15.61/2.50      | m1_subset_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(X2_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X2_49)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(X2_49)
% 15.61/2.50      | ~ v1_funct_1(X0_50) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_6]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1379,plain,
% 15.61/2.50      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ m1_pre_topc(sK3,X1_49)
% 15.61/2.50      | m1_subset_1(k3_tmap_1(X1_49,sK1,sK3,X0_49,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_466]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1660,plain,
% 15.61/2.50      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0_49,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1379]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_2032,plain,
% 15.61/2.50      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1660]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_9,plain,
% 15.61/2.50      ( ~ v5_pre_topc(X0,X1,X2)
% 15.61/2.50      | v5_pre_topc(k2_tmap_1(X1,X2,X0,X3),X3,X2)
% 15.61/2.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.61/2.50      | ~ m1_pre_topc(X3,X1)
% 15.61/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.61/2.50      | v2_struct_0(X1)
% 15.61/2.50      | v2_struct_0(X2)
% 15.61/2.50      | v2_struct_0(X3)
% 15.61/2.50      | ~ l1_pre_topc(X1)
% 15.61/2.50      | ~ l1_pre_topc(X2)
% 15.61/2.50      | ~ v2_pre_topc(X1)
% 15.61/2.50      | ~ v2_pre_topc(X2)
% 15.61/2.50      | ~ v1_funct_1(X0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_463,plain,
% 15.61/2.50      ( ~ v5_pre_topc(X0_50,X0_49,X1_49)
% 15.61/2.50      | v5_pre_topc(k2_tmap_1(X0_49,X1_49,X0_50,X2_49),X2_49,X1_49)
% 15.61/2.50      | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 15.61/2.50      | ~ m1_pre_topc(X2_49,X0_49)
% 15.61/2.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 15.61/2.50      | v2_struct_0(X2_49)
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X0_49)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(X0_49)
% 15.61/2.50      | ~ v1_funct_1(X0_50) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_9]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1403,plain,
% 15.61/2.50      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
% 15.61/2.50      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_49),X0_49,sK1)
% 15.61/2.50      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK2)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | v2_struct_0(sK2)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK2)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK2)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_463]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1998,plain,
% 15.61/2.50      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
% 15.61/2.50      | v5_pre_topc(k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4),sK4,sK1)
% 15.61/2.50      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK2)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK2)
% 15.61/2.50      | v2_struct_0(sK4)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK2)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK2)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1403]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1374,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ m1_pre_topc(sK2,X1_49)
% 15.61/2.50      | m1_subset_1(k3_tmap_1(X1_49,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_466]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1652,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1374]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1986,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK0)
% 15.61/2.50      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1652]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_7,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.61/2.50      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 15.61/2.50      | ~ m1_pre_topc(X4,X3)
% 15.61/2.50      | ~ m1_pre_topc(X1,X3)
% 15.61/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.61/2.50      | v2_struct_0(X3)
% 15.61/2.50      | v2_struct_0(X2)
% 15.61/2.50      | ~ l1_pre_topc(X3)
% 15.61/2.50      | ~ l1_pre_topc(X2)
% 15.61/2.50      | ~ v2_pre_topc(X3)
% 15.61/2.50      | ~ v2_pre_topc(X2)
% 15.61/2.50      | ~ v1_funct_1(X0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_465,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 15.61/2.50      | v1_funct_2(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),u1_struct_0(X3_49),u1_struct_0(X1_49))
% 15.61/2.50      | ~ m1_pre_topc(X3_49,X2_49)
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X2_49)
% 15.61/2.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 15.61/2.50      | v2_struct_0(X2_49)
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X2_49)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(X2_49)
% 15.61/2.50      | ~ v1_funct_1(X0_50) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_7]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1369,plain,
% 15.61/2.50      ( v1_funct_2(k3_tmap_1(X0_49,sK1,sK3,X1_49,sK5),u1_struct_0(X1_49),u1_struct_0(sK1))
% 15.61/2.50      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X1_49,X0_49)
% 15.61/2.50      | ~ m1_pre_topc(sK3,X0_49)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X0_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X0_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_465]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1639,plain,
% 15.61/2.50      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0_49,sK5),u1_struct_0(X0_49),u1_struct_0(sK1))
% 15.61/2.50      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1369]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1970,plain,
% 15.61/2.50      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
% 15.61/2.50      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1639]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1364,plain,
% 15.61/2.50      ( v1_funct_2(k3_tmap_1(X0_49,sK1,sK2,X1_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(X1_49),u1_struct_0(sK1))
% 15.61/2.50      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X1_49,X0_49)
% 15.61/2.50      | ~ m1_pre_topc(sK2,X0_49)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X0_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X0_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_465]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1631,plain,
% 15.61/2.50      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(X0_49),u1_struct_0(sK1))
% 15.61/2.50      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1364]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1958,plain,
% 15.61/2.50      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
% 15.61/2.50      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK0)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1631]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_4,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.61/2.50      | ~ m1_pre_topc(X3,X1)
% 15.61/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.61/2.50      | v2_struct_0(X1)
% 15.61/2.50      | v2_struct_0(X2)
% 15.61/2.50      | ~ l1_pre_topc(X1)
% 15.61/2.50      | ~ l1_pre_topc(X2)
% 15.61/2.50      | ~ v2_pre_topc(X1)
% 15.61/2.50      | ~ v2_pre_topc(X2)
% 15.61/2.50      | ~ v1_funct_1(X0)
% 15.61/2.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 15.61/2.50      inference(cnf_transformation,[],[f45]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_468,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 15.61/2.50      | ~ m1_pre_topc(X2_49,X0_49)
% 15.61/2.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(X0_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X0_49)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(X0_49)
% 15.61/2.50      | ~ v1_funct_1(X0_50)
% 15.61/2.50      | k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k2_tmap_1(X0_49,X1_49,X0_50,X2_49) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_4]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1354,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK2)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK2)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK2)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK2)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 15.61/2.50      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(X0_49)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),X0_49) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_468]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1946,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK2)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK2)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK2)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK2)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5))
% 15.61/2.50      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK4) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1354]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_8,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.61/2.50      | ~ m1_pre_topc(X3,X4)
% 15.61/2.50      | ~ m1_pre_topc(X1,X4)
% 15.61/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.61/2.50      | v2_struct_0(X4)
% 15.61/2.50      | v2_struct_0(X2)
% 15.61/2.50      | ~ l1_pre_topc(X4)
% 15.61/2.50      | ~ l1_pre_topc(X2)
% 15.61/2.50      | ~ v2_pre_topc(X4)
% 15.61/2.50      | ~ v2_pre_topc(X2)
% 15.61/2.50      | ~ v1_funct_1(X0)
% 15.61/2.50      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 15.61/2.50      inference(cnf_transformation,[],[f47]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_464,plain,
% 15.61/2.50      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X2_49)
% 15.61/2.50      | ~ m1_pre_topc(X3_49,X2_49)
% 15.61/2.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(X2_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X2_49)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(X2_49)
% 15.61/2.50      | ~ v1_funct_1(X0_50)
% 15.61/2.50      | v1_funct_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50)) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_8]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1339,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ m1_pre_topc(sK2,X1_49)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | v1_funct_1(k3_tmap_1(X1_49,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_464]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1610,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0_49,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1339]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1928,plain,
% 15.61/2.50      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK0)
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1610]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_29,negated_conjecture,
% 15.61/2.50      ( m1_pre_topc(sK2,sK0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_443,negated_conjecture,
% 15.61/2.50      ( m1_pre_topc(sK2,sK0) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_29]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1166,plain,
% 15.61/2.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 15.61/2.50      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_2,plain,
% 15.61/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.61/2.50      | ~ l1_pre_topc(X1)
% 15.61/2.50      | ~ v2_pre_topc(X1)
% 15.61/2.50      | v2_pre_topc(X0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_470,plain,
% 15.61/2.50      ( ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | v2_pre_topc(X0_49) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_2]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1139,plain,
% 15.61/2.50      ( m1_pre_topc(X0_49,X1_49) != iProver_top
% 15.61/2.50      | l1_pre_topc(X1_49) != iProver_top
% 15.61/2.50      | v2_pre_topc(X1_49) != iProver_top
% 15.61/2.50      | v2_pre_topc(X0_49) = iProver_top ),
% 15.61/2.50      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1759,plain,
% 15.61/2.50      ( l1_pre_topc(sK0) != iProver_top
% 15.61/2.50      | v2_pre_topc(sK2) = iProver_top
% 15.61/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.61/2.50      inference(superposition,[status(thm)],[c_1166,c_1139]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1760,plain,
% 15.61/2.50      ( ~ l1_pre_topc(sK0) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK0) ),
% 15.61/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_1759]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_3,plain,
% 15.61/2.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_469,plain,
% 15.61/2.50      ( ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | l1_pre_topc(X0_49) ),
% 15.61/2.50      inference(subtyping,[status(esa)],[c_3]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1529,plain,
% 15.61/2.50      ( ~ m1_pre_topc(sK2,X0_49)
% 15.61/2.50      | ~ l1_pre_topc(X0_49)
% 15.61/2.50      | l1_pre_topc(sK2) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_469]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1740,plain,
% 15.61/2.50      ( ~ m1_pre_topc(sK2,sK0) | l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1529]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1344,plain,
% 15.61/2.50      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,X1_49)
% 15.61/2.50      | ~ m1_pre_topc(sK3,X1_49)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(X1_49)
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | ~ l1_pre_topc(X1_49)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(X1_49)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | v1_funct_1(k3_tmap_1(X1_49,sK1,sK3,X0_49,sK5))
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_464]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1513,plain,
% 15.61/2.50      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(X0_49,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0_49,sK5))
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1344]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1554,plain,
% 15.61/2.50      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_pre_topc(sK4,sK0)
% 15.61/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.61/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 15.61/2.50      | v2_struct_0(sK1)
% 15.61/2.50      | v2_struct_0(sK0)
% 15.61/2.50      | ~ l1_pre_topc(sK1)
% 15.61/2.50      | ~ l1_pre_topc(sK0)
% 15.61/2.50      | ~ v2_pre_topc(sK1)
% 15.61/2.50      | ~ v2_pre_topc(sK0)
% 15.61/2.50      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
% 15.61/2.50      | ~ v1_funct_1(sK5) ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1513]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_480,plain,
% 15.61/2.50      ( X0_50 != X1_50
% 15.61/2.50      | k3_tmap_1(X0_49,X1_49,X2_49,X3_49,X0_50) = k3_tmap_1(X0_49,X1_49,X2_49,X3_49,X1_50) ),
% 15.61/2.50      theory(equality) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1445,plain,
% 15.61/2.50      ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK3,sK4,X0_50)
% 15.61/2.50      | sK5 != X0_50 ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_480]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_1448,plain,
% 15.61/2.50      ( k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK3,sK4,sK5)
% 15.61/2.50      | sK5 != sK5 ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_1445]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_474,plain,( X0_50 = X0_50 ),theory(equality) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_489,plain,
% 15.61/2.50      ( sK5 = sK5 ),
% 15.61/2.50      inference(instantiation,[status(thm)],[c_474]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_15,negated_conjecture,
% 15.61/2.50      ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
% 15.61/2.50      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
% 15.61/2.50      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
% 15.61/2.50      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
% 15.61/2.50      inference(cnf_transformation,[],[f77]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_16,negated_conjecture,
% 15.61/2.50      ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 15.61/2.50      inference(cnf_transformation,[],[f76]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_17,negated_conjecture,
% 15.61/2.50      ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
% 15.61/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_18,negated_conjecture,
% 15.61/2.50      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 15.61/2.50      inference(cnf_transformation,[],[f74]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_19,negated_conjecture,
% 15.61/2.50      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
% 15.61/2.50      inference(cnf_transformation,[],[f73]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_20,negated_conjecture,
% 15.61/2.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 15.61/2.50      inference(cnf_transformation,[],[f72]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_21,negated_conjecture,
% 15.61/2.50      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 15.61/2.50      inference(cnf_transformation,[],[f71]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_22,negated_conjecture,
% 15.61/2.50      ( v1_funct_1(sK5) ),
% 15.61/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_23,negated_conjecture,
% 15.61/2.50      ( m1_pre_topc(sK4,sK2) ),
% 15.61/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_24,negated_conjecture,
% 15.61/2.50      ( m1_pre_topc(sK2,sK3) ),
% 15.61/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_25,negated_conjecture,
% 15.61/2.50      ( m1_pre_topc(sK4,sK0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_26,negated_conjecture,
% 15.61/2.50      ( ~ v2_struct_0(sK4) ),
% 15.61/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_27,negated_conjecture,
% 15.61/2.50      ( m1_pre_topc(sK3,sK0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_28,negated_conjecture,
% 15.61/2.50      ( ~ v2_struct_0(sK3) ),
% 15.61/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_30,negated_conjecture,
% 15.61/2.50      ( ~ v2_struct_0(sK2) ),
% 15.61/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_31,negated_conjecture,
% 15.61/2.50      ( l1_pre_topc(sK1) ),
% 15.61/2.50      inference(cnf_transformation,[],[f61]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_32,negated_conjecture,
% 15.61/2.50      ( v2_pre_topc(sK1) ),
% 15.61/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_33,negated_conjecture,
% 15.61/2.50      ( ~ v2_struct_0(sK1) ),
% 15.61/2.50      inference(cnf_transformation,[],[f59]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_34,negated_conjecture,
% 15.61/2.50      ( l1_pre_topc(sK0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f58]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_35,negated_conjecture,
% 15.61/2.50      ( v2_pre_topc(sK0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f57]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(c_36,negated_conjecture,
% 15.61/2.50      ( ~ v2_struct_0(sK0) ),
% 15.61/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.61/2.50  
% 15.61/2.50  cnf(contradiction,plain,
% 15.61/2.50      ( $false ),
% 15.61/2.50      inference(minisat,
% 15.61/2.50                [status(thm)],
% 15.61/2.50                [c_35870,c_22661,c_4038,c_3821,c_3296,c_2734,c_2055,
% 15.61/2.50                 c_2032,c_1998,c_1986,c_1970,c_1958,c_1946,c_1928,c_1760,
% 15.61/2.50                 c_1740,c_1554,c_1448,c_489,c_15,c_16,c_17,c_18,c_19,
% 15.61/2.50                 c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,
% 15.61/2.50                 c_31,c_32,c_33,c_34,c_35,c_36]) ).
% 15.61/2.50  
% 15.61/2.50  
% 15.61/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.61/2.50  
% 15.61/2.50  ------                               Statistics
% 15.61/2.50  
% 15.61/2.50  ------ Selected
% 15.61/2.50  
% 15.61/2.50  total_time:                             1.731
% 15.61/2.50  
%------------------------------------------------------------------------------

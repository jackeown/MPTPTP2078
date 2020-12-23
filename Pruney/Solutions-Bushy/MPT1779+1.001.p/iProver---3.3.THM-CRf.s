%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1779+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:22 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 373 expanded)
%              Number of clauses        :   65 (  72 expanded)
%              Number of leaves         :   12 ( 164 expanded)
%              Depth                    :   10
%              Number of atoms          : 1172 (8705 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   25 (  10 average)
%              Maximal clause size      :   50 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f12])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f26,plain,(
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
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(cnf_transformation,[],[f8])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,(
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

fof(f20,plain,(
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

fof(f19,plain,(
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

fof(f18,plain,
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

fof(f24,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f16,f23,f22,f21,f20,f19,f18])).

fof(f56,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_678,plain,
    ( ~ v5_pre_topc(X0_47,X0_49,X1_49)
    | v5_pre_topc(X1_47,X0_49,X1_49)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_2904,plain,
    ( v5_pre_topc(X0_47,sK4,sK1)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),sK4,sK1)
    | X0_47 != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_3846,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),sK4,sK1)
    | v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) != k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_2904])).

cnf(c_4,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_665,plain,
    ( ~ r2_funct_2(X0_48,X1_48,X0_47,X1_47)
    | ~ v1_funct_2(X1_47,X0_48,X1_48)
    | ~ v1_funct_2(X0_47,X0_48,X1_48)
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | X1_47 = X0_47 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1661,plain,
    ( ~ r2_funct_2(X0_48,X1_48,X0_47,k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ v1_funct_2(X0_47,X0_48,X1_48)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),X0_48,X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X0_47 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_2402,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X0_47,k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ v1_funct_2(X0_47,u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = X0_47 ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_3220,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | k3_tmap_1(sK0,sK1,sK3,sK4,sK5) = k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_2402])).

cnf(c_5,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k3_tmap_1(X2,X1,X4,X3,X5)),k3_tmap_1(X2,X1,X4,X0,X5))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_664,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,k3_tmap_1(X2_49,X1_49,X4_49,X3_49,X0_47)),k3_tmap_1(X2_49,X1_49,X4_49,X0_49,X0_47))
    | ~ v1_funct_2(X0_47,u1_struct_0(X4_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X4_49,X2_49)
    | ~ m1_pre_topc(X0_49,X3_49)
    | ~ m1_pre_topc(X3_49,X4_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X3_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X4_49)
    | v2_struct_0(X0_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1644,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),k3_tmap_1(sK0,X1_49,sK2,X0_49,k3_tmap_1(sK0,X1_49,X2_49,sK2,X0_47)),k3_tmap_1(sK0,X1_49,X2_49,X0_49,X0_47))
    | ~ v1_funct_2(X0_47,u1_struct_0(X2_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,sK2)
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(X2_49,sK0)
    | ~ m1_pre_topc(sK2,X2_49)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_1909,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_49),k3_tmap_1(sK0,X0_49,sK2,sK4,k3_tmap_1(sK0,X0_49,X1_49,sK2,X0_47)),k3_tmap_1(sK0,X0_49,X1_49,sK4,X0_47))
    | ~ v1_funct_2(X0_47,u1_struct_0(X1_49),u1_struct_0(X0_49))
    | ~ m1_pre_topc(X1_49,sK0)
    | ~ m1_pre_topc(sK2,X1_49)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_49),u1_struct_0(X0_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_2266,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_49),k3_tmap_1(sK0,X0_49,sK2,sK4,k3_tmap_1(sK0,X0_49,sK3,sK2,X0_47)),k3_tmap_1(sK0,X0_49,sK3,sK4,X0_47))
    | ~ v1_funct_2(X0_47,u1_struct_0(sK3),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_2268,plain,
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
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_7,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(k3_tmap_1(X3,X2,X1,X4,X0),X4,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_663,plain,
    ( ~ v5_pre_topc(X0_47,X0_49,X1_49)
    | v5_pre_topc(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_47),X3_49,X1_49)
    | ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X3_49,X0_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X3_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1609,plain,
    ( ~ v5_pre_topc(X0_47,X0_49,X1_49)
    | v5_pre_topc(k3_tmap_1(sK0,X1_49,X0_49,sK4,X0_47),sK4,X1_49)
    | ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK4,X0_49)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(sK4)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_1867,plain,
    ( ~ v5_pre_topc(X0_47,sK2,X0_49)
    | v5_pre_topc(k3_tmap_1(sK0,X0_49,sK2,sK4,X0_47),sK4,X0_49)
    | ~ v1_funct_2(X0_47,u1_struct_0(sK2),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1609])).

cnf(c_2237,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),sK4,sK1)
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1867])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_668,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v1_funct_2(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_47),u1_struct_0(X3_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1559,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v1_funct_2(k3_tmap_1(sK0,X1_49,X0_49,sK4,X0_47),u1_struct_0(sK4),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_1820,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK2),u1_struct_0(X0_49))
    | v1_funct_2(k3_tmap_1(sK0,X0_49,sK2,sK4,X0_47),u1_struct_0(sK4),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_2023,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_669,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | m1_subset_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1594,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK2),u1_struct_0(X0_49))
    | ~ m1_pre_topc(X1_49,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_49))))
    | m1_subset_1(k3_tmap_1(sK0,X0_49,sK2,X1_49,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_49),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1795,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK2),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_49))))
    | m1_subset_1(k3_tmap_1(sK0,X0_49,sK2,sK4,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_1980,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_667,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_47)
    | v1_funct_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_47)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1544,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK2),u1_struct_0(X0_49))
    | ~ m1_pre_topc(X1_49,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47)
    | v1_funct_1(k3_tmap_1(sK0,X0_49,sK2,X1_49,X0_47)) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1752,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK2),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47)
    | v1_funct_1(k3_tmap_1(sK0,X0_49,sK2,sK4,X0_47)) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_1956,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,k3_tmap_1(sK0,sK1,sK3,sK2,sK5)))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_1752])).

cnf(c_1815,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK3),u1_struct_0(X0_49))
    | v1_funct_2(k3_tmap_1(sK0,X0_49,sK3,sK4,X0_47),u1_struct_0(sK4),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_1817,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_1589,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK3),u1_struct_0(X0_49))
    | ~ m1_pre_topc(X1_49,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | m1_subset_1(k3_tmap_1(sK0,X0_49,sK3,X1_49,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_49),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1782,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK3),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | m1_subset_1(k3_tmap_1(sK0,X0_49,sK3,sK4,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_1784,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_1539,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK3),u1_struct_0(X0_49))
    | ~ m1_pre_topc(X1_49,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47)
    | v1_funct_1(k3_tmap_1(sK0,X0_49,sK3,X1_49,X0_47)) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1724,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK3),u1_struct_0(X0_49))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_49))))
    | v2_struct_0(X0_49)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_49)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0_47)
    | v1_funct_1(k3_tmap_1(sK0,X0_49,sK3,sK4,X0_47)) ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_1726,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_10,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),sK4,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,sK5),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK5)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3846,c_3220,c_2268,c_2237,c_2023,c_1980,c_1956,c_1817,c_1784,c_1726,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31])).


%------------------------------------------------------------------------------

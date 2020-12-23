%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1771+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:21 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 736 expanded)
%              Number of clauses        :  135 ( 180 expanded)
%              Number of leaves         :   21 ( 320 expanded)
%              Depth                    :   15
%              Number of atoms          : 1436 (10749 expanded)
%              Number of equality atoms :  127 ( 829 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f19])).

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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(equality_resolution,[],[f53])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f19])).

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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                    & X5 = X6 )
                                 => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                      & X5 = X6 )
                                   => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f28])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),sK6)
        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),sK5)
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                  & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK4,X2),X6)
                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK4,X3),X5)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                    & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X4,sK3),X5)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(sK2,X1,k2_tmap_1(X0,X1,X4,sK2),X6)
                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
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
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X2,sK1,k2_tmap_1(X0,sK1,X4,X2),X6)
                            & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X4,X3),X5)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
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

fof(f38,plain,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f29,f37,f36,f35,f34,f33,f32,f31])).

fof(f63,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_416,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
    | ~ v1_funct_2(X1_52,X0_53,X1_53)
    | ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | X1_52 = X0_52 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3046,plain,
    ( ~ r2_funct_2(X0_53,X1_53,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),X1_52)
    | ~ v1_funct_2(X1_52,X0_53,X1_53)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),X0_53,X1_53)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X1_52)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)))
    | X1_52 = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)) ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_4656,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),k2_tmap_1(X1_51,sK1,X1_52,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(X1_51,sK1,X1_52,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(X1_51,sK1,X1_52,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)))
    | ~ v1_funct_1(k2_tmap_1(X1_51,sK1,X1_52,sK2))
    | k2_tmap_1(X1_51,sK1,X1_52,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)) ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_4658,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_4656])).

cnf(c_438,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,X0_52,X1_52)
    | r1_tmap_1(X0_51,X1_51,X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_1200,plain,
    ( ~ r1_tmap_1(sK2,sK1,X0_52,X1_52)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    | k2_tmap_1(sK0,sK1,sK4,sK2) != X0_52
    | sK6 != X1_52 ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_1862,plain,
    ( ~ r1_tmap_1(sK2,sK1,X0_52,sK5)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    | k2_tmap_1(sK0,sK1,sK4,sK2) != X0_52
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_3204,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_1862])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X3,X2,X1,X4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1087,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_1302,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_51,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_1537,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_2770,plain,
    ( ~ v1_funct_2(k2_tmap_1(X0_51,sK1,X0_52,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(X0_51,sK1,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(X0_51,sK1,X0_52,sK3)) ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_2772,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2770])).

cnf(c_14,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_414,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,X0_52,X1_52)
    | r1_tmap_1(X2_51,X1_51,k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52),X1_52)
    | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_subset_1(X1_52,u1_struct_0(X2_51))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_pre_topc(X2_51,X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X3_51)
    | v2_struct_0(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1085,plain,
    ( ~ r1_tmap_1(X0_51,sK1,X0_52,X1_52)
    | r1_tmap_1(X1_51,sK1,k3_tmap_1(X2_51,sK1,X0_51,X1_51,X0_52),X1_52)
    | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_52,u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X1_51,X2_51)
    | ~ m1_pre_topc(X1_51,X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X2_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X2_51)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(c_1381,plain,
    ( r1_tmap_1(X0_51,sK1,k3_tmap_1(sK0,sK1,sK3,X0_51,X0_52),X1_52)
    | ~ r1_tmap_1(sK3,sK1,X0_52,X1_52)
    | ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_51,sK3)
    | ~ m1_pre_topc(X0_51,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_1605,plain,
    ( ~ r1_tmap_1(sK3,sK1,X0_52,X1_52)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X0_52),X1_52)
    | ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_1734,plain,
    ( ~ r1_tmap_1(sK3,sK1,X0_52,sK5)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X0_52),sK5)
    | ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_2551,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_425,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | m1_subset_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | ~ l1_struct_0(X2_51)
    | ~ l1_struct_0(X1_51)
    | ~ l1_struct_0(X0_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2310,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(X0_51,sK1,X0_52,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_51)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_2312,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2310])).

cnf(c_2269,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | m1_subset_1(k2_tmap_1(X0_51,sK1,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_51)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_2271,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2269])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0_52,X0_53)
    | m1_subset_1(X1_52,X0_53)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_1992,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | m1_subset_1(sK5,u1_struct_0(sK2))
    | sK5 != X0_52 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_2249,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_424,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ l1_struct_0(X2_51)
    | ~ l1_struct_0(X1_51)
    | ~ l1_struct_0(X0_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2156,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(X0_51,sK1,X0_52,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_51)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_2158,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_2136,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(X0_51,sK1,X0_52,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_51)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_2138,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2136])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1090,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_52)) ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_1257,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_51,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0_51,X0_52)) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_1475,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X0_52)) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_2093,plain,
    ( ~ v1_funct_2(k2_tmap_1(X0_51,sK1,X0_52,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(X0_51,sK1,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)))
    | ~ v1_funct_1(k2_tmap_1(X0_51,sK1,X0_52,sK3)) ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_2095,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_404,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1004,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_407,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1001,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_428,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X2_51,X0_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_981,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51)
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1633,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_981])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_36,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_37,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_38,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_39,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1685,plain,
    ( m1_pre_topc(X0_51,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1633,c_34,c_35,c_36,c_37,c_38,c_39,c_44,c_45])).

cnf(c_1686,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51)
    | m1_pre_topc(X0_51,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1685])).

cnf(c_1691,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1004,c_1686])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_partfun1(X0_53,X1_53,X0_52,X2_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_983,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_partfun1(X0_53,X1_53,X0_52,X2_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_1810,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_983])).

cnf(c_2057,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1810,c_44])).

cnf(c_2063,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_2057])).

cnf(c_2065,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2063])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_423,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ l1_struct_0(X2_51)
    | ~ l1_struct_0(X1_51)
    | ~ l1_struct_0(X0_51)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2002,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_51)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_tmap_1(X0_51,sK1,X0_52,sK2)) ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_2004,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2002])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_418,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_991,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_1747,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_991])).

cnf(c_1917,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1747,c_36])).

cnf(c_9,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_419,plain,
    ( l1_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_990,plain,
    ( l1_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1921,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1917,c_990])).

cnf(c_1922,plain,
    ( l1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1921])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_408,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1000,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_1746,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_991])).

cnf(c_1910,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1746,c_36,c_1747])).

cnf(c_1914,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1910,c_990])).

cnf(c_1915,plain,
    ( l1_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1914])).

cnf(c_431,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1401,plain,
    ( X0_52 != X1_52
    | sK6 != X1_52
    | sK6 = X0_52 ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_1587,plain,
    ( X0_52 != sK6
    | sK6 = X0_52
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1825,plain,
    ( sK5 != sK6
    | sK6 = sK5
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_400,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1008,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_1741,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1008,c_990])).

cnf(c_1743,plain,
    ( l1_struct_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1741])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1088,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | v1_funct_2(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_52),u1_struct_0(X2_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_1319,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,X0_51,X0_52),u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_51,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_1559,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(sK1))
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_1707,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(X0_51,sK1,X0_52,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(X0_51,sK1,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(X0_51,sK1,X0_52,sK3)) ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_1709,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_430,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1436,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_13,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_415,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k2_tmap_1(X2_51,X1_51,X0_52,X3_51)),k2_tmap_1(X2_51,X1_51,X0_52,X0_51))
    | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X3_51)
    | v2_struct_0(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1086,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(sK1),k3_tmap_1(X1_51,sK1,X2_51,X0_51,k2_tmap_1(X1_51,sK1,X0_52,X2_51)),k2_tmap_1(X1_51,sK1,X0_52,X0_51))
    | ~ v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1344,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X0_51,sK1,sK3,sK2,k2_tmap_1(X0_51,sK1,X0_52,sK3)),k2_tmap_1(X0_51,sK1,X0_52,sK2))
    | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,X0_51)
    | ~ m1_pre_topc(sK2,X0_51)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52) ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_1346,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_17,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_411,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_66,plain,
    ( l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4658,c_3204,c_2772,c_2551,c_2312,c_2271,c_2249,c_2158,c_2138,c_2095,c_2065,c_2004,c_1922,c_1915,c_1825,c_1743,c_1709,c_1436,c_1346,c_411,c_66,c_15,c_16,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_33])).


%------------------------------------------------------------------------------

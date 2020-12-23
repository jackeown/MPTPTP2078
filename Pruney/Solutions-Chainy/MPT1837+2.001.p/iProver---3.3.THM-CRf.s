%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:29 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  244 (6700 expanded)
%              Number of clauses        :  168 (1223 expanded)
%              Number of leaves         :   15 (3119 expanded)
%              Depth                    :   35
%              Number of atoms          : 2104 (169070 expanded)
%              Number of equality atoms :  758 (10280 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal clause size      :   54 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                              & k1_tsep_1(X0,X2,X3) = X0 )
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
                  & v1_tsep_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                                & k1_tsep_1(X0,X2,X3) = X0 )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
          & k1_tsep_1(X0,X2,X3) = X0
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),X0,X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7)) )
        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),sK7)
        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),X4)
        & k1_tsep_1(X0,X2,X3) = X0
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK7,X3,X1)
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
              & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
              & k1_tsep_1(X0,X2,X3) = X0
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(X5,X3,X1)
              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(X4,X2,X1)
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),X0,X1)
              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5)) )
            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),X5)
            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),sK6)
            & k1_tsep_1(X0,X2,X3) = X0
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(X5,X3,X1)
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK6,X2,X1)
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & v1_tsep_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),X0,X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5)) )
                & r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X4)
                & k1_tsep_1(X0,X2,sK5) = X0
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK5,X1)
                & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & v1_tsep_1(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                      & k1_tsep_1(X0,X2,X3) = X0
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & v1_tsep_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_tsep_1(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),X0,X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X4)
                    & k1_tsep_1(X0,sK4,X3) = X0
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK4,X1)
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & v1_tsep_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & v1_tsep_1(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),X0,sK3)
                          | ~ v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK3))
                          | ~ v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5)) )
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X4)
                        & k1_tsep_1(X0,X2,X3) = X0
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(X5,X3,sK3)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,X2,sK3)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & v1_tsep_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_tsep_1(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                            & k1_tsep_1(X0,X2,X3) = X0
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(sK2,X2,X3) = sK2
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & v1_tsep_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & v1_tsep_1(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    & k1_tsep_1(sK2,sK4,sK5) = sK2
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & v1_tsep_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & v1_tsep_1(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f39,f38,f37,f36,f35,f34])).

fof(f87,plain,(
    k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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
    inference(flattening,[],[f12])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f17])).

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
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f11])).

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
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f24,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f32])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f25,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f29])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f30])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(flattening,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
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
    inference(definition_folding,[],[f19,f25,f24])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
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
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_29,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2011,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2033,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X3_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5073,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)) = iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2033])).

cnf(c_5733,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_5073])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_50,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_51,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_52,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_56,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_58,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_59,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_38,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_61,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5846,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5733,c_50,c_51,c_52,c_56,c_58,c_59,c_61])).

cnf(c_5847,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5846])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2034,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X3_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5072,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)))) = iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_5602,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_5072])).

cnf(c_5866,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5602,c_50,c_51,c_52,c_56,c_58,c_59,c_61])).

cnf(c_5867,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5866])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2027,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X3_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_5079,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_9211,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | m1_pre_topc(sK2,X2_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5867,c_5079])).

cnf(c_11159,plain,
    ( v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | m1_pre_topc(sK2,X2_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9211,c_50,c_51,c_52,c_56,c_58,c_59,c_61,c_5733])).

cnf(c_11160,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | m1_pre_topc(sK2,X2_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
    inference(renaming,[status(thm)],[c_11159])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2028,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_53),u1_struct_0(X3_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X3_55,X2_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_5078,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_53),u1_struct_0(X3_55),u1_struct_0(X1_55)) = iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X3_55,X2_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2028])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2029,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X3_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_5077,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2029])).

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

cnf(c_28,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_590,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
    | u1_struct_0(sK4) != X1
    | u1_struct_0(sK3) != X2
    | sK6 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_28])).

cnf(c_591,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK6)
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_593,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_37,c_36,c_34])).

cnf(c_594,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_593])).

cnf(c_1988,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_594])).

cnf(c_5096,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1988])).

cnf(c_5314,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5096,c_2011])).

cnf(c_7599,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5077,c_5314])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_53,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_54,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_55,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_62,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_63,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2006,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_5112,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2010,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_5116,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2010])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2032,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X3_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5074,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2032])).

cnf(c_5939,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(sK5,X1_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5116,c_5074])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_66,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_67,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6187,plain,
    ( v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,X1_55) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5939,c_53,c_54,c_55,c_59,c_66,c_67])).

cnf(c_6188,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(sK5,X1_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6187])).

cnf(c_6204,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5112,c_6188])).

cnf(c_6331,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6204])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2031,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X1_55)
    | m1_pre_topc(k1_tsep_1(X1_55,X2_55,X0_55),X1_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_5075,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X2_55,X1_55) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_55,X2_55,X0_55),X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_6623,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_5075])).

cnf(c_10918,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7599,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_61,c_62,c_63,c_6331,c_6623])).

cnf(c_10919,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10918])).

cnf(c_10927,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5078,c_10919])).

cnf(c_11565,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10927,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_61,c_62,c_63,c_6331,c_6623])).

cnf(c_11566,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11565])).

cnf(c_11573,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5867,c_11566])).

cnf(c_65,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_69,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_11682,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11573,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69])).

cnf(c_11683,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11682])).

cnf(c_11690,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_11160,c_11683])).

cnf(c_11885,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11690,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_61,c_62,c_63,c_65,c_66,c_67,c_69,c_6331,c_6623])).

cnf(c_11886,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11885])).

cnf(c_11891,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5847,c_11886])).

cnf(c_11902,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11891,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69])).

cnf(c_27,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_570,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
    | u1_struct_0(sK5) != X1
    | u1_struct_0(sK3) != X2
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_27])).

cnf(c_571,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_573,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_33,c_32,c_30])).

cnf(c_574,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_573])).

cnf(c_1989,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_574])).

cnf(c_5095,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1989])).

cnf(c_5305,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5095,c_2011])).

cnf(c_7598,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5077,c_5305])).

cnf(c_10877,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7598,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_61,c_62,c_63,c_6331,c_6623])).

cnf(c_10878,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10877])).

cnf(c_10886,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5078,c_10878])).

cnf(c_11426,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10886,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_61,c_62,c_63,c_6331,c_6623])).

cnf(c_11427,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11426])).

cnf(c_11434,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5867,c_11427])).

cnf(c_11608,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11434,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69])).

cnf(c_11609,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11608])).

cnf(c_11616,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_11160,c_11609])).

cnf(c_11745,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11616,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,c_61,c_62,c_63,c_65,c_66,c_67,c_69,c_6331,c_6623])).

cnf(c_11746,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11745])).

cnf(c_11751,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5847,c_11746])).

cnf(c_11759,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11751,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2021,plain,
    ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55)
    | ~ v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),X1_55,X0_55)
    | ~ v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),X2_55,X0_55)
    | ~ v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X0_55))
    | ~ v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55))
    | ~ m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X0_55))))
    | ~ v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53))
    | ~ v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_5085,plain,
    ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),X1_55,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),X2_55,X0_55) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_9608,plain,
    ( sP0(X0_55,sK5,X0_53,sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_55) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_5085])).

cnf(c_9618,plain,
    ( sP0(X0_55,sK5,X0_53,sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),sK5,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),sK4,X0_55) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9608,c_2011])).

cnf(c_11765,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11759,c_9618])).

cnf(c_11811,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11765,c_11759])).

cnf(c_31,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_68,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11839,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11811,c_66,c_67,c_68,c_69])).

cnf(c_11840,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11839])).

cnf(c_11905,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11902,c_11840])).

cnf(c_35,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_64,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11992,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11905,c_62,c_63,c_64,c_65])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2025,plain,
    ( ~ sP1(X0_55,X1_55,X0_53,X2_55,X3_55)
    | ~ sP0(X3_55,X2_55,X0_53,X1_55,X0_55)
    | v5_pre_topc(X0_53,k1_tsep_1(X0_55,X1_55,X2_55),X3_55) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5081,plain,
    ( sP1(X0_55,X1_55,X0_53,X2_55,X3_55) != iProver_top
    | sP0(X3_55,X2_55,X0_53,X1_55,X0_55) != iProver_top
    | v5_pre_topc(X0_53,k1_tsep_1(X0_55,X1_55,X2_55),X3_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2025])).

cnf(c_7260,plain,
    ( sP1(sK2,sK4,X0_53,sK5,X0_55) != iProver_top
    | sP0(X0_55,sK5,X0_53,sK4,sK2) != iProver_top
    | v5_pre_topc(X0_53,sK2,X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_5081])).

cnf(c_11998,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11992,c_7260])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X0,X1,X3)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ v1_tsep_1(X2,X0)
    | ~ v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_513,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_tsep_1(X5,X6)
    | ~ v1_tsep_1(X7,X6)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X7,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X6)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | X5 != X3
    | X7 != X1
    | X6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_25])).

cnf(c_514,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_tsep_1(X3,X0)
    | ~ v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_1990,plain,
    ( sP1(X0_55,X1_55,X0_53,X2_55,X3_55)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55))
    | ~ v1_tsep_1(X1_55,X0_55)
    | ~ v1_tsep_1(X2_55,X0_55)
    | ~ m1_pre_topc(X1_55,X0_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_514])).

cnf(c_8733,plain,
    ( sP1(X0_55,sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_tsep_1(sK5,X0_55)
    | ~ v1_tsep_1(sK4,X0_55)
    | ~ m1_pre_topc(sK5,X0_55)
    | ~ m1_pre_topc(sK4,X0_55)
    | ~ m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1990])).

cnf(c_8739,plain,
    ( sP1(X0_55,sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
    | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_tsep_1(sK5,X0_55) != iProver_top
    | v1_tsep_1(sK4,X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8733])).

cnf(c_8741,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_tsep_1(sK5,sK2) != iProver_top
    | v1_tsep_1(sK4,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8739])).

cnf(c_5738,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2033])).

cnf(c_6542,plain,
    ( v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,X0_55)
    | ~ m1_pre_topc(sK4,X0_55)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5738])).

cnf(c_6543,plain,
    ( v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6542])).

cnf(c_6545,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6543])).

cnf(c_5737,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2034])).

cnf(c_6379,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,X0_55)
    | ~ m1_pre_topc(sK4,X0_55)
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5737])).

cnf(c_6380,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6379])).

cnf(c_6382,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6380])).

cnf(c_26,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2012,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_5117,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2012])).

cnf(c_5882,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5867,c_5117])).

cnf(c_5890,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5882,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69])).

cnf(c_5891,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5890])).

cnf(c_5897,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5847,c_5891])).

cnf(c_5905,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5897,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69])).

cnf(c_39,negated_conjecture,
    ( v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_60,plain,
    ( v1_tsep_1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_42,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_57,plain,
    ( v1_tsep_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11998,c_8741,c_6545,c_6382,c_6331,c_5905,c_69,c_67,c_66,c_65,c_63,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_53,c_52,c_51,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.78/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.02  
% 3.78/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/1.02  
% 3.78/1.02  ------  iProver source info
% 3.78/1.02  
% 3.78/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.78/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/1.02  git: non_committed_changes: false
% 3.78/1.02  git: last_make_outside_of_git: false
% 3.78/1.02  
% 3.78/1.02  ------ 
% 3.78/1.02  ------ Parsing...
% 3.78/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  ------ Proving...
% 3.78/1.02  ------ Problem Properties 
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  clauses                                 47
% 3.78/1.02  conjectures                             22
% 3.78/1.02  EPR                                     17
% 3.78/1.02  Horn                                    38
% 3.78/1.02  unary                                   21
% 3.78/1.02  binary                                  8
% 3.78/1.02  lits                                    193
% 3.78/1.02  lits eq                                 3
% 3.78/1.02  fd_pure                                 0
% 3.78/1.02  fd_pseudo                               0
% 3.78/1.02  fd_cond                                 0
% 3.78/1.02  fd_pseudo_cond                          0
% 3.78/1.02  AC symbols                              0
% 3.78/1.02  
% 3.78/1.02  ------ Input Options Time Limit: Unbounded
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing...
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.78/1.02  Current options:
% 3.78/1.02  ------ 
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 33 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing...
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 40 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing...
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 45 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing...
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 45 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.78/1.02  
% 3.78/1.02  ------ Proving...
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  % SZS status Theorem for theBenchmark.p
% 3.78/1.02  
% 3.78/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/1.02  
% 3.78/1.02  fof(f7,conjecture,(
% 3.78/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 3.78/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f8,negated_conjecture,(
% 3.78/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 3.78/1.02    inference(negated_conjecture,[],[f7])).
% 3.78/1.02  
% 3.78/1.02  fof(f22,plain,(
% 3.78/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.78/1.02    inference(ennf_transformation,[],[f8])).
% 3.78/1.02  
% 3.78/1.02  fof(f23,plain,(
% 3.78/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.78/1.02    inference(flattening,[],[f22])).
% 3.78/1.02  
% 3.78/1.02  fof(f39,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),sK7) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK7,X3,X1) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f38,plain,(
% 3.78/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),sK6) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK6,X2,X1) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f37,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5))) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X4) & k1_tsep_1(X0,X2,sK5) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(X5,sK5,X1) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & v1_tsep_1(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f36,plain,(
% 3.78/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X4) & k1_tsep_1(X0,sK4,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(X4,sK4,X1) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & v1_tsep_1(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f35,plain,(
% 3.78/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),X0,sK3) | ~v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f34,plain,(
% 3.78/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(sK2,X2,X3) = sK2 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.78/1.02    introduced(choice_axiom,[])).
% 3.78/1.02  
% 3.78/1.02  fof(f40,plain,(
% 3.78/1.02    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) & k1_tsep_1(sK2,sK4,sK5) = sK2 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & v1_tsep_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.78/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f39,f38,f37,f36,f35,f34])).
% 3.78/1.02  
% 3.78/1.02  fof(f87,plain,(
% 3.78/1.02    k1_tsep_1(sK2,sK4,sK5) = sK2),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f2,axiom,(
% 3.78/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.78/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f12,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.78/1.02    inference(ennf_transformation,[],[f2])).
% 3.78/1.02  
% 3.78/1.02  fof(f13,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/1.02    inference(flattening,[],[f12])).
% 3.78/1.02  
% 3.78/1.02  fof(f44,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f13])).
% 3.78/1.02  
% 3.78/1.02  fof(f67,plain,(
% 3.78/1.02    ~v2_struct_0(sK2)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f68,plain,(
% 3.78/1.02    v2_pre_topc(sK2)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f69,plain,(
% 3.78/1.02    l1_pre_topc(sK2)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f73,plain,(
% 3.78/1.02    ~v2_struct_0(sK4)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f75,plain,(
% 3.78/1.02    m1_pre_topc(sK4,sK2)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f76,plain,(
% 3.78/1.02    ~v2_struct_0(sK5)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f78,plain,(
% 3.78/1.02    m1_pre_topc(sK5,sK2)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f45,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f13])).
% 3.78/1.02  
% 3.78/1.02  fof(f4,axiom,(
% 3.78/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.78/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f16,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.78/1.02    inference(ennf_transformation,[],[f4])).
% 3.78/1.02  
% 3.78/1.02  fof(f17,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/1.02    inference(flattening,[],[f16])).
% 3.78/1.02  
% 3.78/1.02  fof(f48,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f17])).
% 3.78/1.02  
% 3.78/1.02  fof(f49,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f17])).
% 3.78/1.02  
% 3.78/1.02  fof(f50,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f17])).
% 3.78/1.02  
% 3.78/1.02  fof(f1,axiom,(
% 3.78/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.78/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f10,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.78/1.02    inference(ennf_transformation,[],[f1])).
% 3.78/1.02  
% 3.78/1.02  fof(f11,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.78/1.02    inference(flattening,[],[f10])).
% 3.78/1.02  
% 3.78/1.02  fof(f27,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.78/1.02    inference(nnf_transformation,[],[f11])).
% 3.78/1.02  
% 3.78/1.02  fof(f41,plain,(
% 3.78/1.02    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f27])).
% 3.78/1.02  
% 3.78/1.02  fof(f88,plain,(
% 3.78/1.02    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f79,plain,(
% 3.78/1.02    v1_funct_1(sK6)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f80,plain,(
% 3.78/1.02    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f82,plain,(
% 3.78/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f70,plain,(
% 3.78/1.02    ~v2_struct_0(sK3)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f71,plain,(
% 3.78/1.02    v2_pre_topc(sK3)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f72,plain,(
% 3.78/1.02    l1_pre_topc(sK3)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f86,plain,(
% 3.78/1.02    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f43,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f13])).
% 3.78/1.02  
% 3.78/1.02  fof(f83,plain,(
% 3.78/1.02    v1_funct_1(sK7)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f84,plain,(
% 3.78/1.02    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f3,axiom,(
% 3.78/1.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.78/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f9,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.78/1.02    inference(pure_predicate_removal,[],[f3])).
% 3.78/1.02  
% 3.78/1.02  fof(f14,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.78/1.02    inference(ennf_transformation,[],[f9])).
% 3.78/1.02  
% 3.78/1.02  fof(f15,plain,(
% 3.78/1.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/1.02    inference(flattening,[],[f14])).
% 3.78/1.02  
% 3.78/1.02  fof(f47,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f15])).
% 3.78/1.02  
% 3.78/1.02  fof(f89,plain,(
% 3.78/1.02    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f24,plain,(
% 3.78/1.02    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 3.78/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.78/1.02  
% 3.78/1.02  fof(f31,plain,(
% 3.78/1.02    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.78/1.02    inference(nnf_transformation,[],[f24])).
% 3.78/1.02  
% 3.78/1.02  fof(f32,plain,(
% 3.78/1.02    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.78/1.02    inference(flattening,[],[f31])).
% 3.78/1.02  
% 3.78/1.02  fof(f33,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.78/1.02    inference(rectify,[],[f32])).
% 3.78/1.02  
% 3.78/1.02  fof(f64,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 3.78/1.02    inference(cnf_transformation,[],[f33])).
% 3.78/1.02  
% 3.78/1.02  fof(f85,plain,(
% 3.78/1.02    v5_pre_topc(sK7,sK5,sK3)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f81,plain,(
% 3.78/1.02    v5_pre_topc(sK6,sK4,sK3)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f25,plain,(
% 3.78/1.02    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 3.78/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.78/1.02  
% 3.78/1.02  fof(f28,plain,(
% 3.78/1.02    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.78/1.02    inference(nnf_transformation,[],[f25])).
% 3.78/1.02  
% 3.78/1.02  fof(f29,plain,(
% 3.78/1.02    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.78/1.02    inference(flattening,[],[f28])).
% 3.78/1.02  
% 3.78/1.02  fof(f30,plain,(
% 3.78/1.02    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 3.78/1.02    inference(rectify,[],[f29])).
% 3.78/1.02  
% 3.78/1.02  fof(f54,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f30])).
% 3.78/1.02  
% 3.78/1.02  fof(f5,axiom,(
% 3.78/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 3.78/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f18,plain,(
% 3.78/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.78/1.02    inference(ennf_transformation,[],[f5])).
% 3.78/1.02  
% 3.78/1.02  fof(f19,plain,(
% 3.78/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/1.02    inference(flattening,[],[f18])).
% 3.78/1.02  
% 3.78/1.02  fof(f26,plain,(
% 3.78/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/1.02    inference(definition_folding,[],[f19,f25,f24])).
% 3.78/1.02  
% 3.78/1.02  fof(f65,plain,(
% 3.78/1.02    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f26])).
% 3.78/1.02  
% 3.78/1.02  fof(f6,axiom,(
% 3.78/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 3.78/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.02  
% 3.78/1.02  fof(f20,plain,(
% 3.78/1.02    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.78/1.02    inference(ennf_transformation,[],[f6])).
% 3.78/1.02  
% 3.78/1.02  fof(f21,plain,(
% 3.78/1.02    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.78/1.02    inference(flattening,[],[f20])).
% 3.78/1.02  
% 3.78/1.02  fof(f66,plain,(
% 3.78/1.02    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.78/1.02    inference(cnf_transformation,[],[f21])).
% 3.78/1.02  
% 3.78/1.02  fof(f90,plain,(
% 3.78/1.02    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f77,plain,(
% 3.78/1.02    v1_tsep_1(sK5,sK2)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  fof(f74,plain,(
% 3.78/1.02    v1_tsep_1(sK4,sK2)),
% 3.78/1.02    inference(cnf_transformation,[],[f40])).
% 3.78/1.02  
% 3.78/1.02  cnf(c_29,negated_conjecture,
% 3.78/1.02      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 3.78/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2011,negated_conjecture,
% 3.78/1.02      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_29]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_3,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.78/1.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.78/1.02      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 3.78/1.02      | ~ m1_pre_topc(X1,X5)
% 3.78/1.02      | ~ m1_pre_topc(X4,X5)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.78/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.78/1.02      | ~ v2_pre_topc(X2)
% 3.78/1.02      | ~ v2_pre_topc(X5)
% 3.78/1.02      | ~ l1_pre_topc(X2)
% 3.78/1.02      | ~ l1_pre_topc(X5)
% 3.78/1.02      | v2_struct_0(X5)
% 3.78/1.02      | v2_struct_0(X2)
% 3.78/1.02      | v2_struct_0(X4)
% 3.78/1.02      | v2_struct_0(X1)
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(X3) ),
% 3.78/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2033,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.78/1.02      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 3.78/1.02      | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))
% 3.78/1.02      | ~ m1_pre_topc(X2_55,X3_55)
% 3.78/1.02      | ~ m1_pre_topc(X0_55,X3_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ v2_pre_topc(X3_55)
% 3.78/1.02      | ~ v2_pre_topc(X1_55)
% 3.78/1.02      | ~ l1_pre_topc(X3_55)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(X3_55)
% 3.78/1.02      | v2_struct_0(X2_55)
% 3.78/1.02      | ~ v1_funct_1(X0_53)
% 3.78/1.02      | ~ v1_funct_1(X1_53) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5073,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)) = iProver_top
% 3.78/1.02      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X3_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X2_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2033]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5733,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_2011,c_5073]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_49,negated_conjecture,
% 3.78/1.02      ( ~ v2_struct_0(sK2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_50,plain,
% 3.78/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_48,negated_conjecture,
% 3.78/1.02      ( v2_pre_topc(sK2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_51,plain,
% 3.78/1.02      ( v2_pre_topc(sK2) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_47,negated_conjecture,
% 3.78/1.02      ( l1_pre_topc(sK2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_52,plain,
% 3.78/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_43,negated_conjecture,
% 3.78/1.02      ( ~ v2_struct_0(sK4) ),
% 3.78/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_56,plain,
% 3.78/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_41,negated_conjecture,
% 3.78/1.02      ( m1_pre_topc(sK4,sK2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_58,plain,
% 3.78/1.02      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_40,negated_conjecture,
% 3.78/1.02      ( ~ v2_struct_0(sK5) ),
% 3.78/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_59,plain,
% 3.78/1.02      ( v2_struct_0(sK5) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_38,negated_conjecture,
% 3.78/1.02      ( m1_pre_topc(sK5,sK2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_61,plain,
% 3.78/1.02      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5846,plain,
% 3.78/1.02      ( v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_5733,c_50,c_51,c_52,c_56,c_58,c_59,c_61]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5847,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_5846]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.78/1.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.78/1.02      | ~ m1_pre_topc(X1,X5)
% 3.78/1.02      | ~ m1_pre_topc(X4,X5)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.78/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.78/1.02      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 3.78/1.02      | ~ v2_pre_topc(X2)
% 3.78/1.02      | ~ v2_pre_topc(X5)
% 3.78/1.02      | ~ l1_pre_topc(X2)
% 3.78/1.02      | ~ l1_pre_topc(X5)
% 3.78/1.02      | v2_struct_0(X5)
% 3.78/1.02      | v2_struct_0(X2)
% 3.78/1.02      | v2_struct_0(X4)
% 3.78/1.02      | v2_struct_0(X1)
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(X3) ),
% 3.78/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2034,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.78/1.02      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 3.78/1.02      | ~ m1_pre_topc(X2_55,X3_55)
% 3.78/1.02      | ~ m1_pre_topc(X0_55,X3_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 3.78/1.02      | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ v2_pre_topc(X3_55)
% 3.78/1.02      | ~ v2_pre_topc(X1_55)
% 3.78/1.02      | ~ l1_pre_topc(X3_55)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(X3_55)
% 3.78/1.02      | v2_struct_0(X2_55)
% 3.78/1.02      | ~ v1_funct_1(X0_53)
% 3.78/1.02      | ~ v1_funct_1(X1_53) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5072,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)))) = iProver_top
% 3.78/1.02      | v2_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X3_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X2_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2034]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5602,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_2011,c_5072]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5866,plain,
% 3.78/1.02      ( v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_5602,c_50,c_51,c_52,c_56,c_58,c_59,c_61]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5867,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_5866]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_9,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.78/1.02      | ~ m1_pre_topc(X3,X4)
% 3.78/1.02      | ~ m1_pre_topc(X1,X4)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.78/1.02      | ~ v2_pre_topc(X2)
% 3.78/1.02      | ~ v2_pre_topc(X4)
% 3.78/1.02      | ~ l1_pre_topc(X2)
% 3.78/1.02      | ~ l1_pre_topc(X4)
% 3.78/1.02      | v2_struct_0(X4)
% 3.78/1.02      | v2_struct_0(X2)
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2027,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.78/1.02      | ~ m1_pre_topc(X2_55,X3_55)
% 3.78/1.02      | ~ m1_pre_topc(X0_55,X3_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ v2_pre_topc(X3_55)
% 3.78/1.02      | ~ v2_pre_topc(X1_55)
% 3.78/1.02      | ~ l1_pre_topc(X3_55)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(X3_55)
% 3.78/1.02      | ~ v1_funct_1(X0_53)
% 3.78/1.02      | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53)) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5079,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X3_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2027]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_9211,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,X2_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X2_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X2_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X2_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5867,c_5079]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11159,plain,
% 3.78/1.02      ( v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,X2_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X2_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X2_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X2_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_9211,c_50,c_51,c_52,c_56,c_58,c_59,c_61,c_5733]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11160,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,X2_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X2_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X2_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X2_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_11159]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_8,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.78/1.02      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.78/1.02      | ~ m1_pre_topc(X4,X3)
% 3.78/1.02      | ~ m1_pre_topc(X1,X3)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.78/1.02      | ~ v2_pre_topc(X2)
% 3.78/1.02      | ~ v2_pre_topc(X3)
% 3.78/1.02      | ~ l1_pre_topc(X2)
% 3.78/1.02      | ~ l1_pre_topc(X3)
% 3.78/1.02      | v2_struct_0(X3)
% 3.78/1.02      | v2_struct_0(X2)
% 3.78/1.02      | ~ v1_funct_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2028,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.78/1.02      | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_53),u1_struct_0(X3_55),u1_struct_0(X1_55))
% 3.78/1.02      | ~ m1_pre_topc(X3_55,X2_55)
% 3.78/1.02      | ~ m1_pre_topc(X0_55,X2_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ v2_pre_topc(X2_55)
% 3.78/1.02      | ~ v2_pre_topc(X1_55)
% 3.78/1.02      | ~ l1_pre_topc(X2_55)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(X2_55)
% 3.78/1.02      | ~ v1_funct_1(X0_53) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5078,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_53),u1_struct_0(X3_55),u1_struct_0(X1_55)) = iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(X3_55,X2_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X2_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X2_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X2_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2028]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_7,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.78/1.02      | ~ m1_pre_topc(X3,X4)
% 3.78/1.02      | ~ m1_pre_topc(X1,X4)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.78/1.02      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.78/1.02      | ~ v2_pre_topc(X2)
% 3.78/1.02      | ~ v2_pre_topc(X4)
% 3.78/1.02      | ~ l1_pre_topc(X2)
% 3.78/1.02      | ~ l1_pre_topc(X4)
% 3.78/1.02      | v2_struct_0(X4)
% 3.78/1.02      | v2_struct_0(X2)
% 3.78/1.02      | ~ v1_funct_1(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2029,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.78/1.02      | ~ m1_pre_topc(X2_55,X3_55)
% 3.78/1.02      | ~ m1_pre_topc(X0_55,X3_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 3.78/1.02      | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ v2_pre_topc(X3_55)
% 3.78/1.02      | ~ v2_pre_topc(X1_55)
% 3.78/1.02      | ~ l1_pre_topc(X3_55)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(X3_55)
% 3.78/1.02      | ~ v1_funct_1(X0_53) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5077,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
% 3.78/1.02      | v2_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X3_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2029]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_1,plain,
% 3.78/1.02      ( ~ r2_funct_2(X0,X1,X2,X3)
% 3.78/1.02      | ~ v1_funct_2(X3,X0,X1)
% 3.78/1.02      | ~ v1_funct_2(X2,X0,X1)
% 3.78/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.78/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.78/1.02      | ~ v1_funct_1(X3)
% 3.78/1.02      | ~ v1_funct_1(X2)
% 3.78/1.02      | X2 = X3 ),
% 3.78/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_28,negated_conjecture,
% 3.78/1.02      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
% 3.78/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_590,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/1.02      | ~ v1_funct_2(X3,X1,X2)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(X3)
% 3.78/1.02      | X3 = X0
% 3.78/1.02      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 3.78/1.02      | u1_struct_0(sK4) != X1
% 3.78/1.02      | u1_struct_0(sK3) != X2
% 3.78/1.02      | sK6 != X3 ),
% 3.78/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_28]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_591,plain,
% 3.78/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.78/1.02      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.78/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_1(sK6)
% 3.78/1.02      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(unflattening,[status(thm)],[c_590]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_37,negated_conjecture,
% 3.78/1.02      ( v1_funct_1(sK6) ),
% 3.78/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_36,negated_conjecture,
% 3.78/1.02      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_34,negated_conjecture,
% 3.78/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.78/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_593,plain,
% 3.78/1.02      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.78/1.02      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_591,c_37,c_36,c_34]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_594,plain,
% 3.78/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.78/1.02      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_593]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_1988,plain,
% 3.78/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.78/1.02      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_594]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5096,plain,
% 3.78/1.02      ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_1988]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5314,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_5096,c_2011]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_7599,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5077,c_5314]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_46,negated_conjecture,
% 3.78/1.02      ( ~ v2_struct_0(sK3) ),
% 3.78/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_53,plain,
% 3.78/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_45,negated_conjecture,
% 3.78/1.02      ( v2_pre_topc(sK3) ),
% 3.78/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_54,plain,
% 3.78/1.02      ( v2_pre_topc(sK3) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_44,negated_conjecture,
% 3.78/1.02      ( l1_pre_topc(sK3) ),
% 3.78/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_55,plain,
% 3.78/1.02      ( l1_pre_topc(sK3) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_62,plain,
% 3.78/1.02      ( v1_funct_1(sK6) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_63,plain,
% 3.78/1.02      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2006,negated_conjecture,
% 3.78/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_34]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5112,plain,
% 3.78/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_30,negated_conjecture,
% 3.78/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.78/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2010,negated_conjecture,
% 3.78/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_30]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5116,plain,
% 3.78/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2010]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_4,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.78/1.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.78/1.02      | ~ m1_pre_topc(X1,X5)
% 3.78/1.02      | ~ m1_pre_topc(X4,X5)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.78/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.78/1.02      | ~ v2_pre_topc(X2)
% 3.78/1.02      | ~ v2_pre_topc(X5)
% 3.78/1.02      | ~ l1_pre_topc(X2)
% 3.78/1.02      | ~ l1_pre_topc(X5)
% 3.78/1.02      | v2_struct_0(X5)
% 3.78/1.02      | v2_struct_0(X2)
% 3.78/1.02      | v2_struct_0(X4)
% 3.78/1.02      | v2_struct_0(X1)
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(X3)
% 3.78/1.02      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2032,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.78/1.02      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 3.78/1.02      | ~ m1_pre_topc(X2_55,X3_55)
% 3.78/1.02      | ~ m1_pre_topc(X0_55,X3_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 3.78/1.02      | ~ v2_pre_topc(X3_55)
% 3.78/1.02      | ~ v2_pre_topc(X1_55)
% 3.78/1.02      | ~ l1_pre_topc(X3_55)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(X3_55)
% 3.78/1.02      | v2_struct_0(X2_55)
% 3.78/1.02      | ~ v1_funct_1(X0_53)
% 3.78/1.02      | ~ v1_funct_1(X1_53)
% 3.78/1.02      | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53)) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5074,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X3_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X3_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X2_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(X1_53) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2032]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5939,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,X1_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5116,c_5074]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_33,negated_conjecture,
% 3.78/1.02      ( v1_funct_1(sK7) ),
% 3.78/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_66,plain,
% 3.78/1.02      ( v1_funct_1(sK7) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_32,negated_conjecture,
% 3.78/1.02      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_67,plain,
% 3.78/1.02      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6187,plain,
% 3.78/1.02      ( v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,X1_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.78/1.02      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_5939,c_53,c_54,c_55,c_59,c_66,c_67]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6188,plain,
% 3.78/1.02      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,X1_55) != iProver_top
% 3.78/1.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v1_funct_1(X0_53) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_6187]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6204,plain,
% 3.78/1.02      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,X0_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5112,c_6188]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6331,plain,
% 3.78/1.02      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_6204]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5,plain,
% 3.78/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.78/1.02      | ~ m1_pre_topc(X2,X1)
% 3.78/1.02      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.78/1.02      | ~ l1_pre_topc(X1)
% 3.78/1.02      | v2_struct_0(X1)
% 3.78/1.02      | v2_struct_0(X2)
% 3.78/1.02      | v2_struct_0(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2031,plain,
% 3.78/1.02      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.78/1.02      | ~ m1_pre_topc(X2_55,X1_55)
% 3.78/1.02      | m1_pre_topc(k1_tsep_1(X1_55,X2_55,X0_55),X1_55)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(X2_55) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5075,plain,
% 3.78/1.02      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(X2_55,X1_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(k1_tsep_1(X1_55,X2_55,X0_55),X1_55) = iProver_top
% 3.78/1.02      | l1_pre_topc(X1_55) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X1_55) = iProver_top
% 3.78/1.02      | v2_struct_0(X2_55) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2031]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6623,plain,
% 3.78/1.02      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,sK2) = iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_2011,c_5075]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_10918,plain,
% 3.78/1.02      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_7599,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,
% 3.78/1.02                 c_61,c_62,c_63,c_6331,c_6623]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_10919,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_10918]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_10927,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5078,c_10919]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11565,plain,
% 3.78/1.02      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_10927,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,
% 3.78/1.02                 c_61,c_62,c_63,c_6331,c_6623]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11566,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_11565]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11573,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5867,c_11566]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_65,plain,
% 3.78/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_69,plain,
% 3.78/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11682,plain,
% 3.78/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11573,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11683,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_11682]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11690,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11160,c_11683]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11885,plain,
% 3.78/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11690,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,
% 3.78/1.02                 c_61,c_62,c_63,c_65,c_66,c_67,c_69,c_6331,c_6623]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11886,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_11885]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11891,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5847,c_11886]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11902,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11891,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_27,negated_conjecture,
% 3.78/1.02      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
% 3.78/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_570,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.78/1.02      | ~ v1_funct_2(X3,X1,X2)
% 3.78/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/1.02      | ~ v1_funct_1(X0)
% 3.78/1.02      | ~ v1_funct_1(X3)
% 3.78/1.02      | X3 = X0
% 3.78/1.02      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 3.78/1.02      | u1_struct_0(sK5) != X1
% 3.78/1.02      | u1_struct_0(sK3) != X2
% 3.78/1.02      | sK7 != X3 ),
% 3.78/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_27]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_571,plain,
% 3.78/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_1(sK7)
% 3.78/1.02      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(unflattening,[status(thm)],[c_570]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_573,plain,
% 3.78/1.02      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.78/1.02      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_571,c_33,c_32,c_30]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_574,plain,
% 3.78/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.78/1.02      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_573]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_1989,plain,
% 3.78/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.78/1.02      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_574]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5095,plain,
% 3.78/1.02      ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_1989]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5305,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_5095,c_2011]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_7598,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5077,c_5305]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_10877,plain,
% 3.78/1.02      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_7598,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,
% 3.78/1.02                 c_61,c_62,c_63,c_6331,c_6623]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_10878,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_10877]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_10886,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5078,c_10878]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11426,plain,
% 3.78/1.02      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_10886,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,
% 3.78/1.02                 c_61,c_62,c_63,c_6331,c_6623]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11427,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_11426]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11434,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5867,c_11427]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11608,plain,
% 3.78/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11434,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11609,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_11608]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11616,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11160,c_11609]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11745,plain,
% 3.78/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11616,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_59,
% 3.78/1.02                 c_61,c_62,c_63,c_65,c_66,c_67,c_69,c_6331,c_6623]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11746,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_11745]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11751,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5847,c_11746]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11759,plain,
% 3.78/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11751,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_15,plain,
% 3.78/1.02      ( sP0(X0,X1,X2,X3,X4)
% 3.78/1.02      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 3.78/1.02      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 3.78/1.02      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 3.78/1.02      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2021,plain,
% 3.78/1.02      ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55)
% 3.78/1.02      | ~ v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),X1_55,X0_55)
% 3.78/1.02      | ~ v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),X2_55,X0_55)
% 3.78/1.02      | ~ v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X0_55))
% 3.78/1.02      | ~ v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55))))
% 3.78/1.02      | ~ m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X0_55))))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53))
% 3.78/1.02      | ~ v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53)) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5085,plain,
% 3.78/1.02      ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55) = iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),X1_55,X0_55) != iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),X2_55,X0_55) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53)) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_9608,plain,
% 3.78/1.02      ( sP0(X0_55,sK5,X0_53,sK4,sK2) = iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_55) != iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_55) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_2011,c_5085]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_9618,plain,
% 3.78/1.02      ( sP0(X0_55,sK5,X0_53,sK4,sK2) = iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),sK5,X0_55) != iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),sK4,X0_55) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53)) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53)) != iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_9608,c_2011]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11765,plain,
% 3.78/1.02      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11759,c_9618]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11811,plain,
% 3.78/1.02      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.78/1.02      | v5_pre_topc(sK7,sK5,sK3) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top ),
% 3.78/1.02      inference(light_normalisation,[status(thm)],[c_11765,c_11759]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_31,negated_conjecture,
% 3.78/1.02      ( v5_pre_topc(sK7,sK5,sK3) ),
% 3.78/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_68,plain,
% 3.78/1.02      ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11839,plain,
% 3.78/1.02      ( v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11811,c_66,c_67,c_68,c_69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11840,plain,
% 3.78/1.02      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.78/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.78/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_11839]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11905,plain,
% 3.78/1.02      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.78/1.02      | v5_pre_topc(sK6,sK4,sK3) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(demodulation,[status(thm)],[c_11902,c_11840]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_35,negated_conjecture,
% 3.78/1.02      ( v5_pre_topc(sK6,sK4,sK3) ),
% 3.78/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_64,plain,
% 3.78/1.02      ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11992,plain,
% 3.78/1.02      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11905,c_62,c_63,c_64,c_65]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11,plain,
% 3.78/1.02      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.78/1.02      | ~ sP0(X4,X3,X2,X1,X0)
% 3.78/1.02      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 3.78/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2025,plain,
% 3.78/1.02      ( ~ sP1(X0_55,X1_55,X0_53,X2_55,X3_55)
% 3.78/1.02      | ~ sP0(X3_55,X2_55,X0_53,X1_55,X0_55)
% 3.78/1.02      | v5_pre_topc(X0_53,k1_tsep_1(X0_55,X1_55,X2_55),X3_55) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5081,plain,
% 3.78/1.02      ( sP1(X0_55,X1_55,X0_53,X2_55,X3_55) != iProver_top
% 3.78/1.02      | sP0(X3_55,X2_55,X0_53,X1_55,X0_55) != iProver_top
% 3.78/1.02      | v5_pre_topc(X0_53,k1_tsep_1(X0_55,X1_55,X2_55),X3_55) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2025]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_7260,plain,
% 3.78/1.02      ( sP1(sK2,sK4,X0_53,sK5,X0_55) != iProver_top
% 3.78/1.02      | sP0(X0_55,sK5,X0_53,sK4,sK2) != iProver_top
% 3.78/1.02      | v5_pre_topc(X0_53,sK2,X0_55) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_2011,c_5081]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_11998,plain,
% 3.78/1.02      ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
% 3.78/1.02      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_11992,c_7260]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_24,plain,
% 3.78/1.02      ( sP1(X0,X1,X2,X3,X4)
% 3.78/1.02      | ~ r4_tsep_1(X0,X1,X3)
% 3.78/1.02      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.78/1.02      | ~ m1_pre_topc(X3,X0)
% 3.78/1.02      | ~ m1_pre_topc(X1,X0)
% 3.78/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.78/1.02      | ~ v2_pre_topc(X4)
% 3.78/1.02      | ~ v2_pre_topc(X0)
% 3.78/1.02      | ~ l1_pre_topc(X4)
% 3.78/1.02      | ~ l1_pre_topc(X0)
% 3.78/1.02      | v2_struct_0(X0)
% 3.78/1.02      | v2_struct_0(X4)
% 3.78/1.02      | v2_struct_0(X1)
% 3.78/1.02      | v2_struct_0(X3)
% 3.78/1.02      | ~ v1_funct_1(X2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_25,plain,
% 3.78/1.02      ( r4_tsep_1(X0,X1,X2)
% 3.78/1.02      | ~ v1_tsep_1(X2,X0)
% 3.78/1.02      | ~ v1_tsep_1(X1,X0)
% 3.78/1.02      | ~ m1_pre_topc(X2,X0)
% 3.78/1.02      | ~ m1_pre_topc(X1,X0)
% 3.78/1.02      | ~ v2_pre_topc(X0)
% 3.78/1.02      | ~ l1_pre_topc(X0)
% 3.78/1.02      | v2_struct_0(X0) ),
% 3.78/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_513,plain,
% 3.78/1.02      ( sP1(X0,X1,X2,X3,X4)
% 3.78/1.02      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.78/1.02      | ~ v1_tsep_1(X5,X6)
% 3.78/1.02      | ~ v1_tsep_1(X7,X6)
% 3.78/1.02      | ~ m1_pre_topc(X3,X0)
% 3.78/1.02      | ~ m1_pre_topc(X1,X0)
% 3.78/1.02      | ~ m1_pre_topc(X5,X6)
% 3.78/1.02      | ~ m1_pre_topc(X7,X6)
% 3.78/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.78/1.02      | ~ v2_pre_topc(X0)
% 3.78/1.02      | ~ v2_pre_topc(X6)
% 3.78/1.02      | ~ v2_pre_topc(X4)
% 3.78/1.02      | ~ l1_pre_topc(X0)
% 3.78/1.02      | ~ l1_pre_topc(X6)
% 3.78/1.02      | ~ l1_pre_topc(X4)
% 3.78/1.02      | v2_struct_0(X0)
% 3.78/1.02      | v2_struct_0(X1)
% 3.78/1.02      | v2_struct_0(X3)
% 3.78/1.02      | v2_struct_0(X6)
% 3.78/1.02      | v2_struct_0(X4)
% 3.78/1.02      | ~ v1_funct_1(X2)
% 3.78/1.02      | X5 != X3
% 3.78/1.02      | X7 != X1
% 3.78/1.02      | X6 != X0 ),
% 3.78/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_25]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_514,plain,
% 3.78/1.02      ( sP1(X0,X1,X2,X3,X4)
% 3.78/1.02      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.78/1.02      | ~ v1_tsep_1(X3,X0)
% 3.78/1.02      | ~ v1_tsep_1(X1,X0)
% 3.78/1.02      | ~ m1_pre_topc(X3,X0)
% 3.78/1.02      | ~ m1_pre_topc(X1,X0)
% 3.78/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.78/1.02      | ~ v2_pre_topc(X0)
% 3.78/1.02      | ~ v2_pre_topc(X4)
% 3.78/1.02      | ~ l1_pre_topc(X0)
% 3.78/1.02      | ~ l1_pre_topc(X4)
% 3.78/1.02      | v2_struct_0(X0)
% 3.78/1.02      | v2_struct_0(X1)
% 3.78/1.02      | v2_struct_0(X3)
% 3.78/1.02      | v2_struct_0(X4)
% 3.78/1.02      | ~ v1_funct_1(X2) ),
% 3.78/1.02      inference(unflattening,[status(thm)],[c_513]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_1990,plain,
% 3.78/1.02      ( sP1(X0_55,X1_55,X0_53,X2_55,X3_55)
% 3.78/1.02      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55))
% 3.78/1.02      | ~ v1_tsep_1(X1_55,X0_55)
% 3.78/1.02      | ~ v1_tsep_1(X2_55,X0_55)
% 3.78/1.02      | ~ m1_pre_topc(X1_55,X0_55)
% 3.78/1.02      | ~ m1_pre_topc(X2_55,X0_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55))))
% 3.78/1.02      | ~ v2_pre_topc(X0_55)
% 3.78/1.02      | ~ v2_pre_topc(X3_55)
% 3.78/1.02      | ~ l1_pre_topc(X0_55)
% 3.78/1.02      | ~ l1_pre_topc(X3_55)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(X3_55)
% 3.78/1.02      | v2_struct_0(X2_55)
% 3.78/1.02      | ~ v1_funct_1(X0_53) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_514]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_8733,plain,
% 3.78/1.02      ( sP1(X0_55,sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
% 3.78/1.02      | ~ v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))
% 3.78/1.02      | ~ v1_tsep_1(sK5,X0_55)
% 3.78/1.02      | ~ v1_tsep_1(sK4,X0_55)
% 3.78/1.02      | ~ m1_pre_topc(sK5,X0_55)
% 3.78/1.02      | ~ m1_pre_topc(sK4,X0_55)
% 3.78/1.02      | ~ m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v2_pre_topc(X0_55)
% 3.78/1.02      | ~ v2_pre_topc(sK3)
% 3.78/1.02      | ~ l1_pre_topc(X0_55)
% 3.78/1.02      | ~ l1_pre_topc(sK3)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(sK5)
% 3.78/1.02      | v2_struct_0(sK4)
% 3.78/1.02      | v2_struct_0(sK3)
% 3.78/1.02      | ~ v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_1990]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_8739,plain,
% 3.78/1.02      ( sP1(X0_55,sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_tsep_1(sK5,X0_55) != iProver_top
% 3.78/1.02      | v1_tsep_1(sK4,X0_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,X0_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,X0_55) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_8733]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_8741,plain,
% 3.78/1.02      ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_tsep_1(sK5,sK2) != iProver_top
% 3.78/1.02      | v1_tsep_1(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_8739]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5738,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3))
% 3.78/1.02      | v1_funct_2(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))
% 3.78/1.02      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_pre_topc(X0_55,X1_55)
% 3.78/1.02      | ~ m1_pre_topc(sK5,X1_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 3.78/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v2_pre_topc(X1_55)
% 3.78/1.02      | ~ v2_pre_topc(sK3)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | ~ l1_pre_topc(sK3)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(sK5)
% 3.78/1.02      | v2_struct_0(sK3)
% 3.78/1.02      | ~ v1_funct_1(X0_53)
% 3.78/1.02      | ~ v1_funct_1(sK7) ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_2033]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6542,plain,
% 3.78/1.02      ( v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))
% 3.78/1.02      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_pre_topc(sK5,X0_55)
% 3.78/1.02      | ~ m1_pre_topc(sK4,X0_55)
% 3.78/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v2_pre_topc(X0_55)
% 3.78/1.02      | ~ v2_pre_topc(sK3)
% 3.78/1.02      | ~ l1_pre_topc(X0_55)
% 3.78/1.02      | ~ l1_pre_topc(sK3)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(sK5)
% 3.78/1.02      | v2_struct_0(sK4)
% 3.78/1.02      | v2_struct_0(sK3)
% 3.78/1.02      | ~ v1_funct_1(sK7)
% 3.78/1.02      | ~ v1_funct_1(sK6) ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_5738]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6543,plain,
% 3.78/1.02      ( v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,X0_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,X0_55) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_6542]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6545,plain,
% 3.78/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_6543]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5737,plain,
% 3.78/1.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3))
% 3.78/1.02      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_pre_topc(X0_55,X1_55)
% 3.78/1.02      | ~ m1_pre_topc(sK5,X1_55)
% 3.78/1.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 3.78/1.02      | m1_subset_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))))
% 3.78/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v2_pre_topc(X1_55)
% 3.78/1.02      | ~ v2_pre_topc(sK3)
% 3.78/1.02      | ~ l1_pre_topc(X1_55)
% 3.78/1.02      | ~ l1_pre_topc(sK3)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(X1_55)
% 3.78/1.02      | v2_struct_0(sK5)
% 3.78/1.02      | v2_struct_0(sK3)
% 3.78/1.02      | ~ v1_funct_1(X0_53)
% 3.78/1.02      | ~ v1_funct_1(sK7) ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_2034]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6379,plain,
% 3.78/1.02      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.78/1.02      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_pre_topc(sK5,X0_55)
% 3.78/1.02      | ~ m1_pre_topc(sK4,X0_55)
% 3.78/1.02      | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))))
% 3.78/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.78/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v2_pre_topc(X0_55)
% 3.78/1.02      | ~ v2_pre_topc(sK3)
% 3.78/1.02      | ~ l1_pre_topc(X0_55)
% 3.78/1.02      | ~ l1_pre_topc(sK3)
% 3.78/1.02      | v2_struct_0(X0_55)
% 3.78/1.02      | v2_struct_0(sK5)
% 3.78/1.02      | v2_struct_0(sK4)
% 3.78/1.02      | v2_struct_0(sK3)
% 3.78/1.02      | ~ v1_funct_1(sK7)
% 3.78/1.02      | ~ v1_funct_1(sK6) ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_5737]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6380,plain,
% 3.78/1.02      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,X0_55) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,X0_55) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(X0_55) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(X0_55) = iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_6379]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_6382,plain,
% 3.78/1.02      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.78/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.78/1.02      | v2_struct_0(sK5) = iProver_top
% 3.78/1.02      | v2_struct_0(sK4) = iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v2_struct_0(sK2) = iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(instantiation,[status(thm)],[c_6380]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_26,negated_conjecture,
% 3.78/1.02      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 3.78/1.02      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(cnf_transformation,[],[f90]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_2012,negated_conjecture,
% 3.78/1.02      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 3.78/1.02      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 3.78/1.02      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.78/1.02      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.78/1.02      inference(subtyping,[status(esa)],[c_26]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5117,plain,
% 3.78/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_2012]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5882,plain,
% 3.78/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5867,c_5117]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5890,plain,
% 3.78/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_5882,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5891,plain,
% 3.78/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.78/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.78/1.02      inference(renaming,[status(thm)],[c_5890]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5897,plain,
% 3.78/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.78/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.78/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.78/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.78/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.78/1.02      | v2_struct_0(sK3) = iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.78/1.02      | v1_funct_1(sK7) != iProver_top
% 3.78/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.78/1.02      inference(superposition,[status(thm)],[c_5847,c_5891]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_5905,plain,
% 3.78/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.78/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.78/1.02      inference(global_propositional_subsumption,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_5897,c_53,c_54,c_55,c_62,c_63,c_65,c_66,c_67,c_69]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_39,negated_conjecture,
% 3.78/1.02      ( v1_tsep_1(sK5,sK2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_60,plain,
% 3.78/1.02      ( v1_tsep_1(sK5,sK2) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_42,negated_conjecture,
% 3.78/1.02      ( v1_tsep_1(sK4,sK2) ),
% 3.78/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(c_57,plain,
% 3.78/1.02      ( v1_tsep_1(sK4,sK2) = iProver_top ),
% 3.78/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.78/1.02  
% 3.78/1.02  cnf(contradiction,plain,
% 3.78/1.02      ( $false ),
% 3.78/1.02      inference(minisat,
% 3.78/1.02                [status(thm)],
% 3.78/1.02                [c_11998,c_8741,c_6545,c_6382,c_6331,c_5905,c_69,c_67,
% 3.78/1.02                 c_66,c_65,c_63,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_55,
% 3.78/1.02                 c_54,c_53,c_52,c_51,c_50]) ).
% 3.78/1.02  
% 3.78/1.02  
% 3.78/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/1.02  
% 3.78/1.02  ------                               Statistics
% 3.78/1.02  
% 3.78/1.02  ------ Selected
% 3.78/1.02  
% 3.78/1.02  total_time:                             0.449
% 3.78/1.02  
%------------------------------------------------------------------------------

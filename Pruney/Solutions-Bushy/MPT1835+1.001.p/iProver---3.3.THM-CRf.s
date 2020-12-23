%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1835+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:36 EST 2020

% Result     : Theorem 39.50s
% Output     : CNFRefutation 39.50s
% Verified   : 
% Statistics : Number of formulae       :  338 (26374 expanded)
%              Number of clauses        :  249 (5104 expanded)
%              Number of leaves         :   19 (12149 expanded)
%              Depth                    :   45
%              Number of atoms          : 2505 (637213 expanded)
%              Number of equality atoms : 1084 (33590 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   52 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
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
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
                   => ( k1_tsep_1(X0,X2,X3) = X0
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
                             => ( ( r4_tsep_1(X0,X2,X3)
                                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f38,plain,(
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r4_tsep_1(X0,X2,X3)
          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),X0,X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7)) )
        & r4_tsep_1(X0,X2,X3)
        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),sK7)
        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),X4)
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK7,X3,X1)
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
              & r4_tsep_1(X0,X2,X3)
              & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
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
            & r4_tsep_1(X0,X2,X3)
            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),X5)
            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),sK6)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(X5,X3,X1)
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK6,X2,X1)
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                  & r4_tsep_1(X0,X2,X3)
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & k1_tsep_1(X0,X2,X3) = X0
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),X0,X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5)) )
                & r4_tsep_1(X0,X2,sK5)
                & r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X4)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK5,X1)
                & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & k1_tsep_1(X0,X2,sK5) = X0
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                      & r4_tsep_1(X0,X2,X3)
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & k1_tsep_1(X0,X2,X3) = X0
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),X0,X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5)) )
                    & r4_tsep_1(X0,sK4,X3)
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X4)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK4,X1)
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & k1_tsep_1(X0,sK4,X3) = X0
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),X0,sK3)
                          | ~ v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK3))
                          | ~ v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5)) )
                        & r4_tsep_1(X0,X2,X3)
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X4)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(X5,X3,sK3)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,X2,sK3)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & k1_tsep_1(X0,X2,X3) = X0
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
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
                            & r4_tsep_1(X0,X2,X3)
                            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK2,X2,X3)
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(sK2,X2,X3) = sK2
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r4_tsep_1(sK2,sK4,sK5)
    & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)
    & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & k1_tsep_1(sK2,sK4,sK5) = sK2
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f39,f55,f54,f53,f52,f51,f50])).

fof(f100,plain,(
    k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
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

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f108,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f104,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f101,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f102,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f105,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f58,plain,(
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

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f112,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(ennf_transformation,[],[f3])).

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

fof(f59,plain,(
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

fof(f11,axiom,(
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

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f40,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP0(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f47,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f48,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f48])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f41,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      <=> sP0(X1,X4,X2,X0,X3) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f44,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f45,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
            & v5_pre_topc(X2,X1,X4)
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,X1,X4)
          | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f45])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X1,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f46])).

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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
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

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X3,X0,X2,X4,X1)
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f37,f41,f40])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X3,X0,X2,X4,X1)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f111,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_45,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1446,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(subtyping,[status(esa)],[c_45])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X1,X4,X0,X3),u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1467,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v1_funct_2(X1_56,u1_struct_0(X2_57),u1_struct_0(X1_57))
    | v1_funct_2(k10_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56,X1_56),u1_struct_0(k1_tsep_1(X3_57,X0_57,X2_57)),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X1_56)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X3_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5342,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56,X1_56),u1_struct_0(k1_tsep_1(X3_57,X0_57,X2_57)),u1_struct_0(X1_57)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_8074,plain,
    ( v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),u1_struct_0(sK2),u1_struct_0(X0_57)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_5342])).

cnf(c_55,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_56,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_54,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_57,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_53,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_58,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_62,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_63,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_64,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_65,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_8139,plain,
    ( v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),u1_struct_0(sK2),u1_struct_0(X0_57)) = iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8074,c_56,c_57,c_58,c_62,c_63,c_64,c_65])).

cnf(c_8140,plain,
    ( v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),u1_struct_0(sK2),u1_struct_0(X0_57)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_8139])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X1,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1468,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v1_funct_2(X1_56,u1_struct_0(X2_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | m1_subset_1(k10_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56,X1_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X0_57,X2_57)),u1_struct_0(X1_57))))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X1_56)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X3_57) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5341,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56,X1_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_57,X0_57,X2_57)),u1_struct_0(X1_57)))) = iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_6830,plain,
    ( v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_5341])).

cnf(c_7572,plain,
    ( v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) = iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6830,c_56,c_57,c_58,c_62,c_63,c_64,c_65])).

cnf(c_7573,plain,
    ( v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_7572])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1465,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ m1_pre_topc(X2_57,X1_57)
    | m1_pre_topc(k1_tsep_1(X1_57,X0_57,X2_57),X1_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X2_57)
    | ~ l1_pre_topc(X1_57) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_5344,plain,
    ( m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X2_57,X1_57) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_57,X0_57,X2_57),X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1465])).

cnf(c_6512,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_5344])).

cnf(c_6567,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6512,c_56,c_58,c_62,c_63,c_64,c_65])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1454,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_5382,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1454])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1450,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_5378,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k10_tmap_1(X5,X2,X1,X4,X0,X3))
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1466,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v1_funct_2(X1_56,u1_struct_0(X2_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X2_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X1_56)
    | v1_funct_1(k10_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56,X1_56))
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X3_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_5343,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56,X1_56)) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_7347,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(sK4,X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_57,sK3,sK4,X0_57,sK6,X0_56)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5378,c_5343])).

cnf(c_52,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_59,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_60,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_61,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_66,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_67,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_9266,plain,
    ( v2_pre_topc(X1_57) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_57,sK3,sK4,X0_57,sK6,X0_56)) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | m1_pre_topc(sK4,X1_57) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7347,c_59,c_60,c_61,c_62,c_66,c_67])).

cnf(c_9267,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(sK4,X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_57,sK3,sK4,X0_57,sK6,X0_56)) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_9266])).

cnf(c_9282,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_57) != iProver_top
    | m1_pre_topc(sK4,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_5382,c_9267])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_70,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_71,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_9562,plain,
    ( v1_funct_1(k10_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | m1_pre_topc(sK5,X0_57) != iProver_top
    | m1_pre_topc(sK4,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9282,c_64,c_70,c_71])).

cnf(c_9563,plain,
    ( m1_pre_topc(sK5,X0_57) != iProver_top
    | m1_pre_topc(sK4,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_9562])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1456,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | ~ v1_funct_1(X0_56)
    | k2_partfun1(X0_58,X1_58,X0_56,X2_58) = k7_relat_1(X0_56,X2_58) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_5353,plain,
    ( k2_partfun1(X0_58,X1_58,X0_56,X2_58) = k7_relat_1(X0_56,X2_58)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_7589,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_57),k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),X0_58) = k7_relat_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),X0_58)
    | v1_funct_2(X1_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_5353])).

cnf(c_8432,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_58) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_58)
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5378,c_7589])).

cnf(c_8536,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_58) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_58)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8432,c_59,c_60,c_61,c_66,c_67])).

cnf(c_8537,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_58) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_58)
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8536])).

cnf(c_8547,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58)
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5382,c_8537])).

cnf(c_8627,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8547,c_70,c_71])).

cnf(c_8628,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58)
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8627])).

cnf(c_9574,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58)
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9563,c_8628])).

cnf(c_11845,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_58) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9574,c_56,c_57,c_58,c_63,c_65])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1470,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_pre_topc(X2_57,X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X0_57)
    | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_56,X2_57) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_5339,plain,
    ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_56,X2_57)
    | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_7594,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_57),k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(X1_57)) = k2_tmap_1(sK2,X0_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),X1_57)
    | v1_funct_2(X1_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_5339])).

cnf(c_9626,plain,
    ( v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_57),k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(X1_57)) = k2_tmap_1(sK2,X0_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),X1_57)
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7594,c_56,c_57,c_58])).

cnf(c_9627,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_57),k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(X1_57)) = k2_tmap_1(sK2,X0_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),X1_57)
    | v1_funct_2(X1_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_9626])).

cnf(c_9645,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_57),k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(X1_57)) = k2_tmap_1(sK2,X0_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),X1_57)
    | v1_funct_2(X1_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9627,c_8140])).

cnf(c_9649,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_57)
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5378,c_9645])).

cnf(c_9798,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_57)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9649,c_59,c_60,c_61,c_66,c_67])).

cnf(c_9799,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),X0_57)
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9798])).

cnf(c_9810,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_57)
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5382,c_9799])).

cnf(c_10213,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9810,c_70,c_71])).

cnf(c_10214,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_57)
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10213])).

cnf(c_11850,plain,
    ( k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_57) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57))
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11845,c_10214])).

cnf(c_11932,plain,
    ( k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_57) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57))
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9563,c_11850])).

cnf(c_11940,plain,
    ( m1_pre_topc(X0_57,sK2) != iProver_top
    | k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_57) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11932,c_56,c_57,c_58,c_63,c_65])).

cnf(c_11941,plain,
    ( k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),X0_57) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57))
    | m1_pre_topc(X0_57,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_11940])).

cnf(c_11951,plain,
    ( k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_6567,c_11941])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1461,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | m1_subset_1(k2_tmap_1(X0_57,X1_57,X0_56,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X2_57)
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_funct_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_5348,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_57,X1_57,X0_56,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) = iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1459,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X2_57)
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_funct_1(X0_56)
    | v1_funct_1(k2_tmap_1(X0_57,X1_57,X0_56,X2_57)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_5350,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_57,X1_57,X0_56,X2_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_7185,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_57,X1_57,X0_56,X2_57),u1_struct_0(X2_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X3_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_57,X1_57,X0_56,X2_57)) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_57,X1_57,k2_tmap_1(X0_57,X1_57,X0_56,X2_57),X3_57)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5348,c_5350])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1460,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | v1_funct_2(k2_tmap_1(X0_57,X1_57,X0_56,X2_57),u1_struct_0(X2_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X2_57)
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_funct_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1545,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_57,X1_57,X0_56,X2_57),u1_struct_0(X2_57),u1_struct_0(X1_57)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_1548,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_57,X1_57,X0_56,X2_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_48798,plain,
    ( v1_funct_1(X0_56) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X3_57) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_57,X1_57,k2_tmap_1(X0_57,X1_57,X0_56,X2_57),X3_57)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7185,c_1545,c_1548])).

cnf(c_48799,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X3_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(X3_57,X1_57,k2_tmap_1(X0_57,X1_57,X0_56,X3_57),X2_57)) = iProver_top ),
    inference(renaming,[status(thm)],[c_48798])).

cnf(c_48814,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2)),X0_57)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11951,c_48799])).

cnf(c_42,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_68,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_69,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_38,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_72,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_73,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_33,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1455,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_5383,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_7588,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_5383])).

cnf(c_7908,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7588,c_59,c_60,c_61,c_66,c_67,c_69,c_70,c_71,c_73])).

cnf(c_7909,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7908])).

cnf(c_8155,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8140,c_7909])).

cnf(c_8318,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8155,c_59,c_60,c_61,c_66,c_67,c_69,c_70,c_71,c_73])).

cnf(c_6184,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_pre_topc(X0_57,X1_57)
    | ~ m1_pre_topc(sK4,X1_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_56)
    | v1_funct_1(k10_tmap_1(X1_57,sK3,sK4,X0_57,sK6,X0_56))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_7949,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,X0_57)
    | ~ m1_pre_topc(sK4,X0_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v1_funct_1(k10_tmap_1(X0_57,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_6184])).

cnf(c_12492,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7949])).

cnf(c_12493,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12492])).

cnf(c_1443,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_48])).

cnf(c_5372,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1443])).

cnf(c_11949,plain,
    ( k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_5372,c_11941])).

cnf(c_12498,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11949,c_5348])).

cnf(c_13,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_125,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_127,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_1458,plain,
    ( l1_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_5960,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_5961,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5960])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1457,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ l1_pre_topc(X1_57)
    | l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_5352,plain,
    ( m1_pre_topc(X0_57,X1_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_6108,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5372,c_5352])).

cnf(c_5979,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_5980,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5979])).

cnf(c_6316,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6108,c_58,c_63,c_5980])).

cnf(c_5351,plain,
    ( l1_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_6321,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6316,c_5351])).

cnf(c_13580,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12498,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_69,c_70,c_71,c_73,c_127,c_5961,c_6321,c_12493])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1469,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X3_57)
    | ~ v1_funct_1(X0_56)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X3_57)
    | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5340,plain,
    ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56)
    | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1469])).

cnf(c_7593,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_57),k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(X1_57)) = k3_tmap_1(X2_57,X0_57,sK2,X1_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56))
    | v1_funct_2(X1_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_pre_topc(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X2_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X2_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X2_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_5340])).

cnf(c_10348,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_57),k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56),u1_struct_0(X1_57)) = k3_tmap_1(X2_57,X0_57,sK2,X1_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56))
    | v1_funct_2(X1_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_pre_topc(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X2_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X0_56,X1_56)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X2_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X2_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7593,c_8140])).

cnf(c_10352,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56))
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5378,c_10348])).

cnf(c_10517,plain,
    ( v2_pre_topc(X1_57) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56))
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10352,c_59,c_60,c_61,c_66,c_67])).

cnf(c_10518,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56),u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56))
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_56)) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_10517])).

cnf(c_10534,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_5382,c_10518])).

cnf(c_10675,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | l1_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10534,c_70,c_71])).

cnf(c_10676,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_10675])).

cnf(c_11849,plain,
    ( k3_tmap_1(X0_57,sK3,sK2,X1_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X1_57))
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11845,c_10676])).

cnf(c_20235,plain,
    ( v2_struct_0(X0_57) = iProver_top
    | m1_pre_topc(sK2,X0_57) != iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | k3_tmap_1(X0_57,sK3,sK2,X1_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X1_57))
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11849,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_69,c_70,c_71,c_73,c_12493])).

cnf(c_20236,plain,
    ( k3_tmap_1(X0_57,sK3,sK2,X1_57,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(X1_57))
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_20235])).

cnf(c_20249,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4))
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5372,c_20236])).

cnf(c_20345,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20249,c_56,c_57,c_58,c_62,c_63,c_64,c_65,c_6512])).

cnf(c_17,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_642,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_643,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK6)
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_645,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_44,c_43,c_41])).

cnf(c_646,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_645])).

cnf(c_1434,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_646])).

cnf(c_5355,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(c_5713,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5355,c_1446])).

cnf(c_20348,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20345,c_5713])).

cnf(c_7592,plain,
    ( v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),X1_57)) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_5350])).

cnf(c_1551,plain,
    ( l1_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_9579,plain,
    ( l1_struct_0(X1_57) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),X1_57)) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7592,c_56,c_57,c_58,c_62,c_63,c_64,c_65,c_1551,c_5961,c_8074])).

cnf(c_9580,plain,
    ( v1_funct_2(X0_56,u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X1_56,u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,k10_tmap_1(sK2,X0_57,sK4,sK5,X1_56,X0_56),X1_57)) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_9579])).

cnf(c_12500,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4))) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11949,c_9580])).

cnf(c_20363,plain,
    ( m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20348,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_69,c_70,c_71,c_73,c_6321,c_12493,c_12500])).

cnf(c_20364,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20363])).

cnf(c_20370,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13580,c_20364])).

cnf(c_5349,plain,
    ( v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_57,X1_57,X0_56,X2_57),u1_struct_0(X2_57),u1_struct_0(X1_57)) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_12499,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11949,c_5349])).

cnf(c_13268,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12499,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_69,c_70,c_71,c_73,c_127,c_5961,c_6321,c_12493])).

cnf(c_90854,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20370,c_13268])).

cnf(c_90855,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_90854])).

cnf(c_90861,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_90855])).

cnf(c_92177,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_90861,c_59,c_60,c_61,c_66,c_67,c_69,c_70,c_71,c_73])).

cnf(c_92178,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_92177])).

cnf(c_92183,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8140,c_92178])).

cnf(c_92187,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK4)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_92183,c_59,c_60,c_61,c_66,c_67,c_69,c_70,c_71,c_73])).

cnf(c_92194,plain,
    ( k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
    inference(demodulation,[status(thm)],[c_92187,c_11949])).

cnf(c_23,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_19,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,X1,X4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_579,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | k1_tsep_1(X1,X0,X3) != X1
    | sK5 != X3
    | sK4 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_34])).

cnf(c_580,plain,
    ( sP1(sK4,sK2,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | k1_tsep_1(sK2,sK4,sK5) != sK2 ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_584,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | sP1(sK4,sK2,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_55,c_54,c_53,c_49,c_48,c_47,c_46,c_45])).

cnf(c_585,plain,
    ( sP1(sK4,sK2,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_584])).

cnf(c_706,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(X2,X3,X0)
    | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X6))))
    | v2_struct_0(X6)
    | ~ v1_funct_1(X5)
    | ~ l1_pre_topc(X6)
    | ~ v2_pre_topc(X6)
    | X5 != X2
    | X6 != X0
    | sK5 != X1
    | sK4 != X4
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_585])).

cnf(c_707,plain,
    ( ~ sP0(X0,sK5,X1,sK2,sK4)
    | v5_pre_topc(X1,sK2,X0)
    | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_765,plain,
    ( v5_pre_topc(X0,sK2,X1)
    | ~ v5_pre_topc(k2_tmap_1(X2,X3,X4,X5),X5,X3)
    | ~ v5_pre_topc(k2_tmap_1(X2,X3,X4,X6),X6,X3)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ v1_funct_2(k2_tmap_1(X2,X3,X4,X5),u1_struct_0(X5),u1_struct_0(X3))
    | ~ v1_funct_2(k2_tmap_1(X2,X3,X4,X6),u1_struct_0(X6),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(k2_tmap_1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
    | ~ m1_subset_1(k2_tmap_1(X2,X3,X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(X2,X3,X4,X5))
    | ~ v1_funct_1(k2_tmap_1(X2,X3,X4,X6))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | X0 != X4
    | X1 != X3
    | sK5 != X5
    | sK4 != X6
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_707])).

cnf(c_766,plain,
    ( v5_pre_topc(X0,sK2,X1)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X0,sK5),sK5,X1)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X0,sK4),sK4,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ v1_funct_2(k2_tmap_1(sK2,X1,X0,sK5),u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(k2_tmap_1(sK2,X1,X0,sK4),u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X1,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK2,X1,X0,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,X1,X0,sK4))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_1433,plain,
    ( v5_pre_topc(X0_56,sK2,X0_57)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK5),sK5,X0_57)
    | ~ v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK4),sK4,X0_57)
    | ~ v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(X0_57))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK5),u1_struct_0(sK5),u1_struct_0(X0_57))
    | ~ v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK4),u1_struct_0(sK4),u1_struct_0(X0_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_57,X0_56,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57))))
    | ~ m1_subset_1(k2_tmap_1(sK2,X0_57,X0_56,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57))))
    | v2_struct_0(X0_57)
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK5))
    | ~ v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK4))
    | ~ l1_pre_topc(X0_57)
    | ~ v2_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_766])).

cnf(c_5356,plain,
    ( v5_pre_topc(X0_56,sK2,X0_57) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK5),sK5,X0_57) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK4),sK4,X0_57) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK5),u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK4),u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_57,X0_56,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_57,X0_56,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK4)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1433])).

cnf(c_8905,plain,
    ( v5_pre_topc(X0_56,sK2,X0_57) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK5),sK5,X0_57) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK4),sK4,X0_57) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK5),u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK4),u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_57,X0_56,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK4)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_5348,c_5356])).

cnf(c_1445,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_5374,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1445])).

cnf(c_6107,plain,
    ( l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5374,c_5352])).

cnf(c_6002,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_6003,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6002])).

cnf(c_6308,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6107,c_58,c_65,c_6003])).

cnf(c_6313,plain,
    ( l1_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6308,c_5351])).

cnf(c_104344,plain,
    ( m1_subset_1(k2_tmap_1(sK2,X0_57,X0_56,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK4),u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK5),u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK4),sK4,X0_57) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK5),sK5,X0_57) != iProver_top
    | v5_pre_topc(X0_56,sK2,X0_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK4)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8905,c_58,c_1551,c_5961,c_6313])).

cnf(c_104345,plain,
    ( v5_pre_topc(X0_56,sK2,X0_57) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK5),sK5,X0_57) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,X0_57,X0_56,sK4),sK4,X0_57) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(sK2),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK5),u1_struct_0(sK5),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_57,X0_56,sK4),u1_struct_0(sK4),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_57,X0_56,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_57)))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_57,X0_56,sK4)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_104344])).

cnf(c_104366,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5),sK5,sK3) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4),sK4,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_92194,c_104345])).

cnf(c_11948,plain,
    ( k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) ),
    inference(superposition,[status(thm)],[c_5374,c_11941])).

cnf(c_12358,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11948,c_5348])).

cnf(c_13296,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12358,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_69,c_70,c_71,c_73,c_127,c_5961,c_6313,c_12493])).

cnf(c_20248,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5))
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5374,c_20236])).

cnf(c_20325,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20248,c_56,c_57,c_58,c_62,c_63,c_64,c_65,c_6512])).

cnf(c_35,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_622,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_623,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_625,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_40,c_39,c_37])).

cnf(c_626,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_625])).

cnf(c_1435,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_626])).

cnf(c_5354,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_5704,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5354,c_1446])).

cnf(c_20328,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20325,c_5704])).

cnf(c_12360,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5))) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11948,c_9580])).

cnf(c_20333,plain,
    ( m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20328,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_69,c_70,c_71,c_73,c_6313,c_12360,c_12493])).

cnf(c_20334,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20333])).

cnf(c_20340,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13296,c_20334])).

cnf(c_12359,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11948,c_5349])).

cnf(c_13240,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12359,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_69,c_70,c_71,c_73,c_127,c_5961,c_6313,c_12493])).

cnf(c_20378,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20340,c_13240])).

cnf(c_20379,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20378])).

cnf(c_20385,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_20379])).

cnf(c_20857,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20385,c_59,c_60,c_61,c_66,c_67,c_69,c_70,c_71,c_73])).

cnf(c_20858,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_20857])).

cnf(c_20863,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8140,c_20858])).

cnf(c_20868,plain,
    ( k7_relat_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK5)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20863,c_59,c_60,c_61,c_66,c_67,c_69,c_70,c_71,c_73])).

cnf(c_20878,plain,
    ( k2_tmap_1(sK2,sK3,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
    inference(demodulation,[status(thm)],[c_20868,c_11948])).

cnf(c_104381,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_104366,c_20878,c_92194])).

cnf(c_107025,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48814,c_56,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_71,c_72,c_73,c_8318,c_12493,c_104381])).

cnf(c_107026,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_107025])).

cnf(c_107031,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7573,c_107026])).

cnf(c_107037,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_107031,c_59,c_60,c_61,c_66,c_67,c_69,c_70,c_71,c_73])).

cnf(c_107042,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8140,c_107037])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_107042,c_73,c_71,c_70,c_69,c_67,c_66,c_61,c_60,c_59])).


%------------------------------------------------------------------------------

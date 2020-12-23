%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1829+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:34 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :  347 (11290 expanded)
%              Number of clauses        :  260 (2257 expanded)
%              Number of leaves         :   15 (4968 expanded)
%              Depth                    :   39
%              Number of atoms          : 3629 (245999 expanded)
%              Number of equality atoms : 1304 (4892 expanded)
%              Maximal formula depth    :   31 (  11 average)
%              Maximal clause size      :   48 (  10 average)
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
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
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
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( r1_tsep_1(X2,X3)
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
                             => ( r4_tsep_1(X0,X2,X3)
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r4_tsep_1(X0,X2,X3)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7)) )
        & r4_tsep_1(X0,X2,X3)
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK7,X3,X1)
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
              & r4_tsep_1(X0,X2,X3)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(X5,X3,X1)
              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(X4,X2,X1)
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_tsep_1(X0,X2,X3),X1)
              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5)) )
            & r4_tsep_1(X0,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(X5,X3,X1)
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK6,X2,X1)
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                  & r4_tsep_1(X0,X2,X3)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & r1_tsep_1(X2,X3)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5)) )
                & r4_tsep_1(X0,X2,sK5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK5,X1)
                & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & r1_tsep_1(X2,sK5)
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                      & r4_tsep_1(X0,X2,X3)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_tsep_1(X0,sK4,X3),X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5)) )
                    & r4_tsep_1(X0,sK4,X3)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK4,X1)
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & r1_tsep_1(sK4,X3)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
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
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),sK3)
                          | ~ v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                          | ~ v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5)) )
                        & r4_tsep_1(X0,X2,X3)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(X5,X3,sK3)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,X2,sK3)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & r1_tsep_1(X2,X3)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r4_tsep_1(X0,X2,X3)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & r1_tsep_1(X2,X3)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK2,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
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

fof(f42,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r4_tsep_1(sK2,sK4,sK5)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & r1_tsep_1(sK4,sK5)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f41,f40,f39,f38,f37,f36])).

fof(f92,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f50,plain,(
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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f25,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(definition_folding,[],[f21,f25,f24])).

fof(f73,plain,(
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

fof(f93,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f55,plain,(
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
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | r1_tsep_1(X2,X3) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(flattening,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(nnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ r1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f43])).

fof(f84,plain,(
    r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
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

fof(f88,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
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

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f51,plain,(
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

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
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

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f58])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ r1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f45])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | ~ r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1562,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_2333,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_1572,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2323,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)) = iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1572])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_546,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
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
    | ~ v1_funct_1(X2)
    | sK5 != X3
    | sK4 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_547,plain,
    ( sP1(sK2,sK4,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_51,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_50,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_49,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_551,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | sP1(sK2,sK4,X0,sK5,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_51,c_50,c_49,c_45,c_44,c_43,c_42])).

cnf(c_552,plain,
    ( sP1(sK2,sK4,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_551])).

cnf(c_587,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X4,X3,X1)),u1_struct_0(X0))
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X4,X3,X1)),u1_struct_0(X0))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | v2_struct_0(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X2)
    | X5 != X2
    | X6 != X0
    | sK5 != X1
    | sK4 != X3
    | sK2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_552])).

cnf(c_588,plain,
    ( sP0(X0,sK5,X1,sK4,sK2)
    | ~ v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_968,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_588])).

cnf(c_969,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_968])).

cnf(c_1539,plain,
    ( ~ v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55)
    | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_969])).

cnf(c_2356,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1539])).

cnf(c_52,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_53,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_54,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_58,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_59,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_60,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_61,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1570,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X1_55)
    | m1_pre_topc(k1_tsep_1(X1_55,X2_55,X0_55),X1_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X2_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3196,plain,
    ( ~ m1_pre_topc(X0_55,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_55,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_3393,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3196])).

cnf(c_3394,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3393])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_1567,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_54),u1_struct_0(X3_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X3_55,X2_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3225,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v1_funct_2(k3_tmap_1(sK2,X1_55,X0_55,sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_3797,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_3225])).

cnf(c_3798,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3797])).

cnf(c_12199,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2356,c_52,c_53,c_54,c_58,c_59,c_60,c_61,c_3394,c_3798])).

cnf(c_5,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(k10_tmap_1(X2,X1,X0,X3,X4,X5),u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))
    | ~ r1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k10_tmap_1(X2,X1,X0,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k10_tmap_1(X2,X1,X0,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_41,negated_conjecture,
    ( r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_809,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(k10_tmap_1(X2,X1,X0,X3,X4,X5),u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k10_tmap_1(X2,X1,X0,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X0,X3)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k10_tmap_1(X2,X1,X0,X3,X4,X5))
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_41])).

cnf(c_810,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK4,k10_tmap_1(X1,X0,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_2(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3)) ),
    inference(unflattening,[status(thm)],[c_809])).

cnf(c_814,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK4,k10_tmap_1(X1,X0,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_2(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_810,c_45,c_43])).

cnf(c_815,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK4,k10_tmap_1(X1,X0,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_2(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3)) ),
    inference(renaming,[status(thm)],[c_814])).

cnf(c_1542,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_55),k3_tmap_1(X1_55,X0_55,k1_tsep_1(X1_55,sK4,sK5),sK4,k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54)),X0_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ v1_funct_2(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54),u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_pre_topc(sK4,X1_55)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | ~ v1_funct_1(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_815])).

cnf(c_2353,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_55),k3_tmap_1(X1_55,X0_55,k1_tsep_1(X1_55,sK4,sK5),sK4,k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54)),X0_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54),u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(sK5,X1_55) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1542])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_1568,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2327,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1558,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_2337,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_15,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1564,plain,
    ( ~ r2_funct_2(X0_56,X1_56,X0_54,X1_54)
    | ~ v1_funct_2(X1_54,X0_56,X1_56)
    | ~ v1_funct_2(X0_54,X0_56,X1_56)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | X1_54 = X0_54 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2331,plain,
    ( X0_54 = X1_54
    | r2_funct_2(X0_56,X1_56,X1_54,X0_54) != iProver_top
    | v1_funct_2(X1_54,X0_56,X1_56) != iProver_top
    | v1_funct_2(X0_54,X0_56,X1_56) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_5768,plain,
    ( sK6 = X0_54
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_54,sK6) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2337,c_2331])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_63,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_64,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6020,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | sK6 = X0_54
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_54,sK6) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5768,c_63,c_64])).

cnf(c_6021,plain,
    ( sK6 = X0_54
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_54,sK6) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6020])).

cnf(c_7894,plain,
    ( k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54) = sK6
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54),sK6) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X1_55),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2327,c_6021])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_55,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_56,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_57,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_10413,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X1_55),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54),sK6) != iProver_top
    | k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54) = sK6
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7894,c_55,c_56,c_57])).

cnf(c_10414,plain,
    ( k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54) = sK6
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54),sK6) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X1_55),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,X1_55,sK4,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10413])).

cnf(c_10429,plain,
    ( k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_55,sK4,sK5),X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_10414])).

cnf(c_66,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_11733,plain,
    ( v1_funct_1(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54))) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_55,sK4,sK5),X0_55) != iProver_top
    | k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10429,c_55,c_56,c_57,c_63,c_64,c_66])).

cnf(c_11734,plain,
    ( k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_55,sK4,sK5),X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,X0_54))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11733])).

cnf(c_12212,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12199,c_11734])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_1573,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2322,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)))) = iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1573])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_938,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_588])).

cnf(c_939,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_1540,plain,
    ( ~ v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55)
    | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) ),
    inference(subtyping,[status(esa)],[c_939])).

cnf(c_2355,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1540])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_1566,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3215,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(sK2,X1_55,X0_55,sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_3737,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) ),
    inference(instantiation,[status(thm)],[c_3215])).

cnf(c_3738,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3737])).

cnf(c_11966,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2355,c_52,c_53,c_54,c_58,c_59,c_60,c_61,c_3394,c_3738])).

cnf(c_11980,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_11966])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f49])).

cnf(c_1571,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3245,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | v1_funct_1(k10_tmap_1(sK2,X1_55,sK4,X0_55,X1_54,X0_54)) ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_3906,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54)) ),
    inference(instantiation,[status(thm)],[c_3245])).

cnf(c_3907,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3906])).

cnf(c_3255,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X1_55))
    | v1_funct_2(k10_tmap_1(sK2,X1_55,sK4,X0_55,X1_54,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,X0_55)),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_4218,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X0_55))
    | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(instantiation,[status(thm)],[c_3255])).

cnf(c_4219,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4218])).

cnf(c_17574,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11980,c_52,c_53,c_54,c_58,c_59,c_60,c_61,c_3907,c_4219])).

cnf(c_17575,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54))) = iProver_top ),
    inference(renaming,[status(thm)],[c_17574])).

cnf(c_26,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1028,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_588])).

cnf(c_1029,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_1028])).

cnf(c_1537,plain,
    ( ~ v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55)
    | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1029])).

cnf(c_2358,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1537])).

cnf(c_3235,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k3_tmap_1(sK2,X1_55,X0_55,sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_3861,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_3235])).

cnf(c_3862,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3861])).

cnf(c_12217,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2358,c_52,c_53,c_54,c_58,c_59,c_60,c_61,c_3394,c_3862])).

cnf(c_12234,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54) = sK6
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK6) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12217,c_6021])).

cnf(c_12772,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK6) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54) = sK6
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12234,c_55,c_56,c_57])).

cnf(c_12773,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54) = sK6
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK6) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12772])).

cnf(c_12785,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_12773])).

cnf(c_12840,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12785,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_3394,c_12212])).

cnf(c_12841,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12840])).

cnf(c_12854,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_12841])).

cnf(c_22933,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12854,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66])).

cnf(c_22934,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54))) != iProver_top ),
    inference(renaming,[status(thm)],[c_22933])).

cnf(c_22946,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_17575,c_22934])).

cnf(c_23098,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12212,c_55,c_56,c_57,c_63,c_64,c_66,c_22946])).

cnf(c_23099,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_23098])).

cnf(c_23110,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_23099])).

cnf(c_25960,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23110,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66])).

cnf(c_25961,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) = sK6
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_25960])).

cnf(c_25971,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_25961])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_67,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_68,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_70,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4178,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3906])).

cnf(c_4179,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4178])).

cnf(c_4181,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
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
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4179])).

cnf(c_14,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1565,plain,
    ( r2_funct_2(X0_56,X1_56,X0_54,X0_54)
    | ~ v1_funct_2(X0_54,X0_56,X1_56)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2330,plain,
    ( r2_funct_2(X0_56,X1_56,X0_54,X0_54) = iProver_top
    | v1_funct_2(X0_54,X0_56,X1_56) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1565])).

cnf(c_12231,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12217,c_2330])).

cnf(c_12501,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12231,c_52,c_53,c_54,c_58,c_59,c_60,c_61,c_3394,c_3738,c_12199])).

cnf(c_12502,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_12501])).

cnf(c_3,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(k10_tmap_1(X2,X1,X3,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
    | ~ r1_tsep_1(X3,X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(k10_tmap_1(X2,X1,X3,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k10_tmap_1(X2,X1,X3,X0,X4,X5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_671,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(k10_tmap_1(X2,X1,X3,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(k10_tmap_1(X2,X1,X3,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(k10_tmap_1(X2,X1,X3,X0,X4,X5))
    | sK5 != X0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_41])).

cnf(c_672,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK5,k10_tmap_1(X1,X0,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_2(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3)) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_676,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK5,k10_tmap_1(X1,X0,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_2(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_45,c_43])).

cnf(c_677,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK5,k10_tmap_1(X1,X0,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ v1_funct_2(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k10_tmap_1(X1,X0,sK4,sK5,X2,X3)) ),
    inference(renaming,[status(thm)],[c_676])).

cnf(c_1544,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_55),k3_tmap_1(X1_55,X0_55,k1_tsep_1(X1_55,sK4,sK5),sK5,k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54)),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ v1_funct_2(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54),u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_pre_topc(sK4,X1_55)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | ~ v1_funct_1(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_677])).

cnf(c_2351,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_55),k3_tmap_1(X1_55,X0_55,k1_tsep_1(X1_55,sK4,sK5),sK5,k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54)),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54),u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(sK5,X1_55) != iProver_top
    | m1_pre_topc(sK4,X1_55) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_55,X0_55,sK4,sK5,X0_54,X1_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1148,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_588])).

cnf(c_1149,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_1148])).

cnf(c_1533,plain,
    ( ~ v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55)
    | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1149])).

cnf(c_2362,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_3230,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k3_tmap_1(sK2,X1_55,X0_55,sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_3827,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_3230])).

cnf(c_3828,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3827])).

cnf(c_12991,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2362,c_52,c_53,c_54,c_58,c_59,c_60,c_61,c_3394,c_3828])).

cnf(c_5767,plain,
    ( sK7 = X0_54
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_54,sK7) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_2331])).

cnf(c_6006,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | sK7 = X0_54
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_54,sK7) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5767,c_67,c_68])).

cnf(c_6007,plain,
    ( sK7 = X0_54
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_54,sK7) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6006])).

cnf(c_13008,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54) = sK7
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK7) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12991,c_6007])).

cnf(c_13285,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK7) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54) = sK7
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13008,c_55,c_56,c_57])).

cnf(c_13286,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54) = sK7
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK7) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13285])).

cnf(c_13298,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) = sK7
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2351,c_13286])).

cnf(c_5885,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4218])).

cnf(c_5886,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5885])).

cnf(c_3265,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
    | m1_subset_1(k10_tmap_1(sK2,X1_55,sK4,X0_55,X1_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_55)),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_4278,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(instantiation,[status(thm)],[c_3265])).

cnf(c_5940,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4278])).

cnf(c_5941,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5940])).

cnf(c_3210,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(sK2,X1_55,X0_55,sK5,X0_54)) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_3707,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) ),
    inference(instantiation,[status(thm)],[c_3210])).

cnf(c_11833,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))) ),
    inference(instantiation,[status(thm)],[c_3707])).

cnf(c_11834,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11833])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1088,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),u1_struct_0(X5),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_588])).

cnf(c_1089,plain,
    ( ~ v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),u1_struct_0(sK5),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_1088])).

cnf(c_1535,plain,
    ( ~ v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55)
    | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1089])).

cnf(c_2360,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1535])).

cnf(c_3220,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v1_funct_2(k3_tmap_1(sK2,X1_55,X0_55,sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_3767,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_3220])).

cnf(c_3768,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3767])).

cnf(c_12973,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2360,c_52,c_53,c_54,c_58,c_59,c_60,c_61,c_3394,c_3768])).

cnf(c_7893,plain,
    ( k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54) = sK7
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54),sK7) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X1_55),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2327,c_6007])).

cnf(c_10333,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X1_55),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54),sK7) != iProver_top
    | k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54) = sK7
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7893,c_55,c_56,c_57])).

cnf(c_10334,plain,
    ( k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54) = sK7
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54),sK7) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X1_55),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,X1_55,sK5,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10333])).

cnf(c_10349,plain,
    ( k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)) = sK7
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_55,sK4,sK5),X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2351,c_10334])).

cnf(c_11034,plain,
    ( v1_funct_1(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7))) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_55,sK4,sK5),X0_55) != iProver_top
    | k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)) = sK7
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10349,c_55,c_56,c_57,c_67,c_68,c_70])).

cnf(c_11035,plain,
    ( k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)) = sK7
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_55,sK4,sK5),X0_55) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,sK3,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,sK3,sK4,sK5,X0_54,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11034])).

cnf(c_12986,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) = sK7
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12973,c_11035])).

cnf(c_13966,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) = sK7
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13298,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_67,c_68,c_70,c_3394,c_4179,c_5886,c_5941,c_11834,c_12986])).

cnf(c_13967,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) = sK7
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_13966])).

cnf(c_13976,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2337,c_13967])).

cnf(c_5888,plain,
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
    inference(instantiation,[status(thm)],[c_5886])).

cnf(c_5943,plain,
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
    inference(instantiation,[status(thm)],[c_5941])).

cnf(c_11836,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11834])).

cnf(c_12988,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12986])).

cnf(c_14039,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13976,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66,c_67,c_68,c_70,c_3394,c_4181,c_5888,c_5943,c_11836,c_12988])).

cnf(c_1,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
    | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X6)
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
    | ~ r1_tsep_1(X3,X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | k10_tmap_1(X2,X1,X3,X0,X6,X5) = X4 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_737,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,X4),X5)
    | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,X4),X6)
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X0)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | k10_tmap_1(X2,X1,X3,X0,X6,X5) = X4
    | sK5 != X0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_41])).

cnf(c_738,plain,
    ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK5,X2),X3)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK4,X2),X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k10_tmap_1(X1,X0,sK4,sK5,X4,X3) = X2 ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_742,plain,
    ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK5,X2),X3)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK4,X2),X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k10_tmap_1(X1,X0,sK4,sK5,X4,X3) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_738,c_45,c_43])).

cnf(c_743,plain,
    ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK5,X2),X3)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK4,sK5),sK4,X2),X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
    | ~ m1_pre_topc(sK5,X1)
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK4,sK5)),u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k10_tmap_1(X1,X0,sK4,sK5,X4,X3) = X2 ),
    inference(renaming,[status(thm)],[c_742])).

cnf(c_1543,plain,
    ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_55),k3_tmap_1(X1_55,X0_55,k1_tsep_1(X1_55,sK4,sK5),sK5,X0_54),X1_54)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_55),k3_tmap_1(X1_55,X0_55,k1_tsep_1(X1_55,sK4,sK5),sK4,X0_54),X2_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(X2_54,u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_pre_topc(sK4,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X2_54)
    | ~ v1_funct_1(X1_54)
    | k10_tmap_1(X1_55,X0_55,sK4,sK5,X2_54,X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_743])).

cnf(c_2352,plain,
    ( k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54) = X2_54
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK5,X2_54),X1_54) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK4,X2_54),X0_54) != iProver_top
    | v1_funct_2(X2_54,u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1543])).

cnf(c_14054,plain,
    ( k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,X1_54) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,X1_54) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),X0_54) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14039,c_2352])).

cnf(c_14986,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),X0_54) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,X1_54) != iProver_top
    | k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,X1_54) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14054,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66,c_67,c_68,c_70,c_4181,c_5888,c_5943])).

cnf(c_14987,plain,
    ( k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,X1_54) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,X1_54) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),X0_54) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_14986])).

cnf(c_15003,plain,
    ( k10_tmap_1(sK2,sK3,sK4,sK5,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),X0_54) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12502,c_14987])).

cnf(c_11940,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))) ),
    inference(instantiation,[status(thm)],[c_3737])).

cnf(c_11941,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11940])).

cnf(c_11943,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11941])).

cnf(c_12699,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) ),
    inference(instantiation,[status(thm)],[c_3797])).

cnf(c_12700,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12699])).

cnf(c_12702,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12700])).

cnf(c_12761,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) ),
    inference(instantiation,[status(thm)],[c_3861])).

cnf(c_12762,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12761])).

cnf(c_12764,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12762])).

cnf(c_23365,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,X0_54) != iProver_top
    | k10_tmap_1(sK2,sK3,sK4,sK5,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),X0_54) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15003,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66,c_67,c_68,c_70,c_3394,c_4181,c_5888,c_5943,c_11943,c_12702,c_12764])).

cnf(c_23366,plain,
    ( k10_tmap_1(sK2,sK3,sK4,sK5,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),X0_54) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_23365])).

cnf(c_23376,plain,
    ( k10_tmap_1(sK2,sK3,sK4,sK5,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,sK7) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_23366])).

cnf(c_3180,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,sK7)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_3181,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),sK7,sK7) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3180])).

cnf(c_23445,plain,
    ( k10_tmap_1(sK2,sK3,sK4,sK5,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23376,c_67,c_68,c_70,c_3181])).

cnf(c_23450,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_23445,c_2323])).

cnf(c_24073,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23450,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66,c_67,c_68,c_70,c_5888])).

cnf(c_24080,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_24073,c_23099])).

cnf(c_26040,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25971,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66,c_67,c_68,c_70,c_4181,c_24080])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_17,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_621,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | v2_struct_0(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X1
    | sK4 != X3
    | sK2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_552])).

cnf(c_622,plain,
    ( ~ sP0(X0,sK5,X1,sK4,sK2)
    | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_887,plain,
    ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),X5,X3)
    | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),X4,X3)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),u1_struct_0(X5),u1_struct_0(X3))
    | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
    | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6))
    | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_622])).

cnf(c_888,plain,
    ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),sK5,X1)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),sK4,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0))
    | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_887])).

cnf(c_1541,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK5,X0_55)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK4,X0_55)
    | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54))
    | ~ v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) ),
    inference(subtyping,[status(esa)],[c_888])).

cnf(c_2354,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK5,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK4,X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_1655,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK5,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK4,X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_3708,plain,
    ( v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3707])).

cnf(c_11236,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK5,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK4,X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2354,c_52,c_53,c_54,c_58,c_59,c_60,c_61,c_1655,c_3394,c_3708,c_3738,c_3768,c_3798,c_3828,c_3862])).

cnf(c_14049,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14039,c_11236])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_69,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1563,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2332,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1563])).

cnf(c_72,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4191,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2332,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66,c_67,c_68,c_70,c_72,c_4181])).

cnf(c_4192,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4191])).

cnf(c_4435,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
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
    inference(superposition,[status(thm)],[c_2322,c_4192])).

cnf(c_14979,plain,
    ( v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14049,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_61,c_63,c_64,c_66,c_67,c_68,c_69,c_70,c_4181,c_4435,c_5888,c_5943])).

cnf(c_26046,plain,
    ( v5_pre_topc(sK6,sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26040,c_14979])).

cnf(c_38,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_65,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26046,c_65])).


%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1833+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:35 EST 2020

% Result     : Theorem 11.98s
% Output     : CNFRefutation 11.98s
% Verified   : 
% Statistics : Number of formulae       :  302 (6393 expanded)
%              Number of clauses        :  219 (1449 expanded)
%              Number of leaves         :   15 (2657 expanded)
%              Depth                    :   37
%              Number of atoms          : 3326 (139928 expanded)
%              Number of equality atoms : 1226 (5020 expanded)
%              Maximal formula depth    :   31 (  12 average)
%              Maximal clause size      :   50 (  10 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7)) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK7,X3,X1)
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
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
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(X5,X3,X1)
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK6,X2,X1)
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
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
          & v1_tsep_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5)) )
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
        & v1_tsep_1(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
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
              & v1_tsep_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_tsep_1(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_tsep_1(X0,sK4,X3),X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5)) )
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
            & v1_tsep_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & v1_tsep_1(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),sK3)
                          | ~ v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                          | ~ v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5)) )
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
                & v1_tsep_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_tsep_1(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
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

fof(f43,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f42,f41,f40,f39,f38,f37])).

fof(f86,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f26,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(nnf_transformation,[],[f26])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f33])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(nnf_transformation,[],[f12])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f44])).

fof(f87,plain,(
    r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f17])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

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
    inference(nnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f59])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f46])).

fof(f58,plain,(
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

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f43])).

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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
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
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
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
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f22,f26,f25])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_tsep_1(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2181,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_3128,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2181])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2212,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56)
    | ~ l1_pre_topc(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3097,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X2_56,X1_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2212])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2185,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_3124,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2185])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2189,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_3120,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2189])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2205,plain,
    ( ~ sP1(X0_56,X1_56,X0_55,X2_56,X3_56)
    | ~ sP0(X3_56,X2_56,X0_55,X1_56,X0_56)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56)),u1_struct_0(X3_56)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3104,plain,
    ( sP1(X0_56,X1_56,X0_55,X2_56,X3_56) != iProver_top
    | sP0(X3_56,X2_56,X0_55,X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56)),u1_struct_0(X3_56)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2205])).

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
    inference(cnf_transformation,[],[f100])).

cnf(c_40,negated_conjecture,
    ( r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_693,plain,
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
    inference(resolution_lifted,[status(thm)],[c_5,c_40])).

cnf(c_694,plain,
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
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_698,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_694,c_46,c_43])).

cnf(c_699,plain,
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
    inference(renaming,[status(thm)],[c_698])).

cnf(c_2167,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_56),k3_tmap_1(X1_56,X0_56,k1_tsep_1(X1_56,sK4,sK5),sK4,k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55)),X0_55)
    | ~ v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X0_56))
    | ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X0_56))
    | ~ v1_funct_2(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56))
    | ~ m1_pre_topc(sK5,X1_56)
    | ~ m1_pre_topc(sK4,X1_56)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_699])).

cnf(c_3142,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_56),k3_tmap_1(X1_56,X0_56,k1_tsep_1(X1_56,sK4,sK5),sK4,k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55)),X0_55) = iProver_top
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56)) != iProver_top
    | m1_pre_topc(sK5,X1_56) != iProver_top
    | m1_pre_topc(sK4,X1_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2167])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_2210,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | m1_subset_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X3_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X3_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X3_56)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3099,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56)))) = iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2210])).

cnf(c_14,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2207,plain,
    ( r2_funct_2(X0_54,X1_54,X0_55,X0_55)
    | ~ v1_funct_2(X0_55,X0_54,X1_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3102,plain,
    ( r2_funct_2(X0_54,X1_54,X0_55,X0_55) = iProver_top
    | v1_funct_2(X0_55,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2207])).

cnf(c_11880,plain,
    ( r2_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),k3_tmap_1(X2_56,X1_56,X3_56,X0_56,X0_55),k3_tmap_1(X2_56,X1_56,X3_56,X0_56,X0_55)) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X3_56),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_56,X1_56,X3_56,X0_56,X0_55),u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X3_56,X2_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_56,X1_56,X3_56,X0_56,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_3102])).

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
    inference(cnf_transformation,[],[f55])).

cnf(c_2208,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X3_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X3_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X3_56)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3101,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

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
    inference(cnf_transformation,[],[f56])).

cnf(c_2209,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k3_tmap_1(X2_56,X1_56,X0_56,X3_56,X0_55),u1_struct_0(X3_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3100,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_56,X1_56,X0_56,X3_56,X0_55),u1_struct_0(X3_56),u1_struct_0(X1_56)) = iProver_top
    | m1_pre_topc(X3_56,X2_56) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_17388,plain,
    ( r2_funct_2(u1_struct_0(X0_56),u1_struct_0(X1_56),k3_tmap_1(X2_56,X1_56,X3_56,X0_56,X0_55),k3_tmap_1(X2_56,X1_56,X3_56,X0_56,X0_55)) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X3_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X3_56,X2_56) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11880,c_3101,c_3100])).

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
    inference(cnf_transformation,[],[f48])).

cnf(c_621,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1,c_40])).

cnf(c_622,plain,
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
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_626,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_46,c_43])).

cnf(c_627,plain,
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
    inference(renaming,[status(thm)],[c_626])).

cnf(c_2168,plain,
    ( ~ r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_56),k3_tmap_1(X1_56,X0_56,k1_tsep_1(X1_56,sK4,sK5),sK5,X0_55),X1_55)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_56),k3_tmap_1(X1_56,X0_56,k1_tsep_1(X1_56,sK4,sK5),sK4,X0_55),X2_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X0_56))
    | ~ v1_funct_2(X2_55,u1_struct_0(sK4),u1_struct_0(X0_56))
    | ~ m1_pre_topc(sK5,X1_56)
    | ~ m1_pre_topc(sK4,X1_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | ~ m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v1_funct_1(X2_55)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | k10_tmap_1(X1_56,X0_56,sK4,sK5,X2_55,X1_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_627])).

cnf(c_3141,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55) = X2_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,X2_55),X1_55) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK4,X2_55),X0_55) != iProver_top
    | v1_funct_2(X2_55,u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2168])).

cnf(c_17395,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,X1_55)) = X1_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK4,X1_55),X0_55) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,X1_55),u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,X1_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,X1_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17388,c_3141])).

cnf(c_18575,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,X1_55)) = X1_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK4,X1_55),X0_55) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17395,c_3101,c_3099,c_3100])).

cnf(c_18579,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55))) = k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_18575])).

cnf(c_18823,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55))) = k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)
    | sP1(X0_56,sK4,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55),sK5,X1_56) != iProver_top
    | sP0(X1_56,sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55),sK4,X0_56) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3104,c_18579])).

cnf(c_59,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_62,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

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
    inference(cnf_transformation,[],[f51])).

cnf(c_2214,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(X2_56),u1_struct_0(X1_56))
    | v1_funct_2(k10_tmap_1(X3_56,X1_56,X2_56,X0_56,X1_55,X0_55),u1_struct_0(k1_tsep_1(X3_56,X2_56,X0_56)),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X3_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X3_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X3_56)
    | v2_struct_0(X2_56)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3095,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_56),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_56,X1_56,X2_56,X0_56,X1_55,X0_55),u1_struct_0(k1_tsep_1(X3_56,X2_56,X0_56)),u1_struct_0(X1_56)) = iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2214])).

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
    inference(cnf_transformation,[],[f52])).

cnf(c_2215,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(X2_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | m1_subset_1(k10_tmap_1(X3_56,X1_56,X2_56,X0_56,X1_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_56,X2_56,X0_56)),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X3_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X3_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X3_56)
    | v2_struct_0(X2_56)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3094,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_56,X1_56,X2_56,X0_56,X1_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_56,X2_56,X0_56)),u1_struct_0(X1_56)))) = iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2215])).

cnf(c_18824,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55))) = k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_18579])).

cnf(c_21201,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55))) = k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18824,c_59,c_62])).

cnf(c_21202,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55))) = k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21201])).

cnf(c_21226,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55))) = k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_21202])).

cnf(c_21571,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55))) = k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18823,c_59,c_62,c_21226])).

cnf(c_21572,plain,
    ( k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55))) = k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21571])).

cnf(c_21594,plain,
    ( k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) = k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3120,c_21572])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_56,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_57,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_58,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_70,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_71,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_22211,plain,
    ( v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) = k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21594,c_56,c_57,c_58,c_70,c_71])).

cnf(c_22212,plain,
    ( k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) = k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22211])).

cnf(c_22228,plain,
    ( k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7))) = k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7)
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_22212])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_66,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_67,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

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
    inference(cnf_transformation,[],[f50])).

cnf(c_2213,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(X2_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X3_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X3_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X3_56)
    | v2_struct_0(X2_56)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k10_tmap_1(X3_56,X1_56,X2_56,X0_56,X1_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3096,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_56,X1_56,X2_56,X0_56,X1_55,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_10045,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(sK5,X1_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_56,sK3,X0_56,sK5,X0_55,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3120,c_3096])).

cnf(c_11148,plain,
    ( v1_funct_1(k10_tmap_1(X1_56,sK3,X0_56,sK5,X0_55,sK7)) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,X1_56) != iProver_top
    | m1_pre_topc(X0_56,X1_56) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10045,c_56,c_57,c_58,c_62,c_70,c_71])).

cnf(c_11149,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(sK5,X1_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_56,sK3,X0_56,sK5,X0_55,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11148])).

cnf(c_11165,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_11149])).

cnf(c_11434,plain,
    ( v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11165,c_59,c_66,c_67])).

cnf(c_11435,plain,
    ( m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11434])).

cnf(c_22351,plain,
    ( k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7))) = k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7)
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22228,c_66,c_67,c_11435])).

cnf(c_22364,plain,
    ( k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7))) = k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7)
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_22351])).

cnf(c_22499,plain,
    ( k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7))) = k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,sK7)
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22364,c_59,c_62])).

cnf(c_22511,plain,
    ( k10_tmap_1(sK2,sK3,sK4,sK5,sK6,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3128,c_22499])).

cnf(c_52,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_53,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_54,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_55,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_44,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_61,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_22514,plain,
    ( k10_tmap_1(sK2,sK3,sK4,sK5,sK6,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) = k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22511,c_53,c_54,c_55,c_61])).

cnf(c_22520,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_22514,c_3094])).

cnf(c_64,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_69,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_73,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4066,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK4),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56))))
    | m1_subset_1(k10_tmap_1(sK2,X1_56,sK4,X0_56,X1_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_56)),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_4984,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(X0_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK4),u1_struct_0(X0_56))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56))))
    | m1_subset_1(k10_tmap_1(sK2,X0_56,sK4,sK5,X1_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_4066])).

cnf(c_6713,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4984])).

cnf(c_6714,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6713])).

cnf(c_6716,plain,
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
    inference(instantiation,[status(thm)],[c_6714])).

cnf(c_24354,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22520,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_61,c_62,c_64,c_66,c_67,c_69,c_70,c_71,c_73,c_6716])).

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
    inference(cnf_transformation,[],[f98])).

cnf(c_555,plain,
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
    inference(resolution_lifted,[status(thm)],[c_3,c_40])).

cnf(c_556,plain,
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
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_560,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_46,c_43])).

cnf(c_561,plain,
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
    inference(renaming,[status(thm)],[c_560])).

cnf(c_2169,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_56),k3_tmap_1(X1_56,X0_56,k1_tsep_1(X1_56,sK4,sK5),sK5,k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55)),X1_55)
    | ~ v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X0_56))
    | ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X0_56))
    | ~ v1_funct_2(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56))
    | ~ m1_pre_topc(sK5,X1_56)
    | ~ m1_pre_topc(sK4,X1_56)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_561])).

cnf(c_3140,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_56),k3_tmap_1(X1_56,X0_56,k1_tsep_1(X1_56,sK4,sK5),sK5,k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55)),X1_55) = iProver_top
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55),u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56)) != iProver_top
    | m1_pre_topc(sK5,X1_56) != iProver_top
    | m1_pre_topc(sK4,X1_56) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_56,sK4,sK5)),u1_struct_0(X0_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_56,X0_56,sK4,sK5,X0_55,X1_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2169])).

cnf(c_15,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2206,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X0_55,X1_55)
    | ~ v1_funct_2(X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X0_55,X0_54,X1_54)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | X1_55 = X0_55 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3103,plain,
    ( X0_55 = X1_55
    | r2_funct_2(X0_54,X1_54,X1_55,X0_55) != iProver_top
    | v1_funct_2(X1_55,X0_54,X1_54) != iProver_top
    | v1_funct_2(X0_55,X0_54,X1_54) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2206])).

cnf(c_10474,plain,
    ( sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3120,c_3103])).

cnf(c_10955,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10474,c_70,c_71])).

cnf(c_10956,plain,
    ( sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_10955])).

cnf(c_11882,plain,
    ( k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55) = sK7
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55),sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_56),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_10956])).

cnf(c_15257,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_56),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55),sK7) != iProver_top
    | k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55) = sK7
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11882,c_56,c_57,c_58])).

cnf(c_15258,plain,
    ( k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55) = sK7
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55),sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_56),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,X1_56,sK5,X0_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15257])).

cnf(c_15273,plain,
    ( k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) = sK7
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3140,c_15258])).

cnf(c_16613,plain,
    ( v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) = sK7
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15273,c_56,c_57,c_58,c_70,c_71,c_73])).

cnf(c_16614,plain,
    ( k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) = sK7
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_16613])).

cnf(c_16635,plain,
    ( k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) = sK7
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_16614])).

cnf(c_20755,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) = sK7
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16635,c_56,c_57,c_58])).

cnf(c_20756,plain,
    ( k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) = sK7
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20755])).

cnf(c_24370,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_24354,c_20756])).

cnf(c_3961,plain,
    ( ~ m1_pre_topc(X0_56,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_56,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2212])).

cnf(c_4182,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3961])).

cnf(c_4183,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4182])).

cnf(c_4046,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK4),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k10_tmap_1(sK2,X1_56,sK4,X0_56,X1_55,X0_55)) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_4736,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(X0_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK4),u1_struct_0(X0_56))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k10_tmap_1(sK2,X0_56,sK4,sK5,X1_55,X0_55)) ),
    inference(instantiation,[status(thm)],[c_4046])).

cnf(c_5128,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4736])).

cnf(c_5129,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5128])).

cnf(c_5131,plain,
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
    inference(instantiation,[status(thm)],[c_5129])).

cnf(c_4056,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK4),u1_struct_0(X1_56))
    | v1_funct_2(k10_tmap_1(sK2,X1_56,sK4,X0_56,X1_55,X0_55),u1_struct_0(k1_tsep_1(sK2,sK4,X0_56)),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_4800,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(X0_56))
    | ~ v1_funct_2(X1_55,u1_struct_0(sK4),u1_struct_0(X0_56))
    | v1_funct_2(k10_tmap_1(sK2,X0_56,sK4,sK5,X1_55,X0_55),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_4056])).

cnf(c_5158,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4800])).

cnf(c_5159,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5158])).

cnf(c_5161,plain,
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
    inference(instantiation,[status(thm)],[c_5159])).

cnf(c_3975,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK2,X1_56,X0_56,sK5,X0_55)) ),
    inference(instantiation,[status(thm)],[c_2208])).

cnf(c_4381,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK2,X0_56,k1_tsep_1(sK2,sK4,sK5),sK5,X0_55)) ),
    inference(instantiation,[status(thm)],[c_3975])).

cnf(c_14442,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_4381])).

cnf(c_14443,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14442])).

cnf(c_14445,plain,
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
    inference(instantiation,[status(thm)],[c_14443])).

cnf(c_26302,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24370,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_61,c_62,c_64,c_66,c_67,c_69,c_70,c_71,c_73,c_4183,c_5131,c_5161,c_6716,c_14445])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_2200,plain,
    ( sP0(X0_56,X1_56,X0_55,X2_56,X3_56)
    | ~ v5_pre_topc(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),X1_56,X0_56)
    | ~ v5_pre_topc(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),X2_56,X0_56)
    | ~ v1_funct_2(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),u1_struct_0(X1_56),u1_struct_0(X0_56))
    | ~ v1_funct_2(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),u1_struct_0(X2_56),u1_struct_0(X0_56))
    | ~ m1_subset_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X0_56))))
    | ~ v1_funct_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55))
    | ~ v1_funct_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3109,plain,
    ( sP0(X0_56,X1_56,X0_55,X2_56,X3_56) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),X1_56,X0_56) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),X2_56,X0_56) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),u1_struct_0(X1_56),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),u1_struct_0(X2_56),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X0_56)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2200])).

cnf(c_26323,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26302,c_3109])).

cnf(c_10475,plain,
    ( sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_3103])).

cnf(c_11109,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10475,c_66,c_67])).

cnf(c_11110,plain,
    ( sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_11109])).

cnf(c_11883,plain,
    ( k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55) = sK6
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55),sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_56),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_11110])).

cnf(c_15360,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_56),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55),sK6) != iProver_top
    | k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55) = sK6
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11883,c_56,c_57,c_58])).

cnf(c_15361,plain,
    ( k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55) = sK6
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55),sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X1_56),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,X1_56,sK4,X0_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15360])).

cnf(c_15376,plain,
    ( k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) = sK6
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_15361])).

cnf(c_16689,plain,
    ( v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55))) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) = sK6
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15376,c_56,c_57,c_58,c_66,c_67,c_69])).

cnf(c_16690,plain,
    ( k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) = sK6
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55))) != iProver_top ),
    inference(renaming,[status(thm)],[c_16689])).

cnf(c_16711,plain,
    ( k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) = sK6
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_16690])).

cnf(c_20836,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) = sK6
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16711,c_56,c_57,c_58])).

cnf(c_20837,plain,
    ( k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) = sK6
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0_56,sK4,sK5),X0_56) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,sK6,X0_55))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20836])).

cnf(c_22531,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22514,c_20837])).

cnf(c_22609,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22531,c_22514])).

cnf(c_3980,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK2,X1_56,X0_56,sK4,X0_55)) ),
    inference(instantiation,[status(thm)],[c_2208])).

cnf(c_4380,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k3_tmap_1(sK2,X0_56,k1_tsep_1(sK2,sK4,sK5),sK4,X0_55)) ),
    inference(instantiation,[status(thm)],[c_3980])).

cnf(c_14432,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))) ),
    inference(instantiation,[status(thm)],[c_4380])).

cnf(c_14433,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14432])).

cnf(c_14435,plain,
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
    inference(instantiation,[status(thm)],[c_14433])).

cnf(c_3985,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k3_tmap_1(sK2,X1_56,X0_56,sK5,X0_55),u1_struct_0(sK5),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_4581,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))
    | v1_funct_2(k3_tmap_1(sK2,X0_56,k1_tsep_1(sK2,sK4,sK5),sK5,X0_55),u1_struct_0(sK5),u1_struct_0(X0_56))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_3985])).

cnf(c_15212,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_4581])).

cnf(c_15213,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15212])).

cnf(c_15215,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15213])).

cnf(c_3995,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | m1_subset_1(k3_tmap_1(sK2,X1_56,X0_56,sK5,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2210])).

cnf(c_4641,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))))
    | m1_subset_1(k3_tmap_1(sK2,X0_56,k1_tsep_1(sK2,sK4,sK5),sK5,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_3995])).

cnf(c_15308,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_4641])).

cnf(c_15309,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15308])).

cnf(c_15311,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15309])).

cnf(c_25788,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22609,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_61,c_62,c_64,c_66,c_67,c_69,c_70,c_71,c_73,c_4183,c_5131,c_5161,c_6716,c_14435,c_14445,c_15215,c_15311])).

cnf(c_26447,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26323,c_25788,c_26302])).

cnf(c_17,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2204,plain,
    ( ~ sP1(X0_56,X1_56,X0_55,X2_56,X3_56)
    | ~ sP0(X3_56,X2_56,X0_55,X1_56,X0_56)
    | v5_pre_topc(X0_55,k1_tsep_1(X0_56,X1_56,X2_56),X3_56) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3105,plain,
    ( sP1(X0_56,X1_56,X0_55,X2_56,X3_56) != iProver_top
    | sP0(X3_56,X2_56,X0_55,X1_56,X0_56) != iProver_top
    | v5_pre_topc(X0_55,k1_tsep_1(X0_56,X1_56,X2_56),X3_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2204])).

cnf(c_31,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2190,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_3119,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2190])).

cnf(c_74,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5718,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3119,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_61,c_62,c_64,c_66,c_67,c_69,c_70,c_71,c_73,c_74,c_5131,c_5161])).

cnf(c_5719,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5718])).

cnf(c_5724,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
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
    inference(superposition,[status(thm)],[c_3094,c_5719])).

cnf(c_5727,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5724,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_61,c_62,c_64,c_66,c_67,c_69,c_70,c_71,c_73])).

cnf(c_8646,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3105,c_5727])).

cnf(c_30,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_tsep_1(X3,X0)
    | ~ v1_tsep_1(X1,X0)
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
    inference(cnf_transformation,[],[f74])).

cnf(c_2191,plain,
    ( sP1(X0_56,X1_56,X0_55,X2_56,X3_56)
    | ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56)),u1_struct_0(X3_56))
    | ~ v1_tsep_1(X1_56,X0_56)
    | ~ v1_tsep_1(X2_56,X0_56)
    | ~ m1_pre_topc(X1_56,X0_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56)),u1_struct_0(X3_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(X3_56)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X3_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X3_56)
    | v2_struct_0(X2_56)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_4036,plain,
    ( sP1(sK2,sK4,X0_55,X0_56,X1_56)
    | ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,X0_56)),u1_struct_0(X1_56))
    | ~ v1_tsep_1(X0_56,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X0_56)),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_4696,plain,
    ( sP1(sK2,sK4,X0_55,sK5,X0_56)
    | ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_4036])).

cnf(c_6618,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),sK5,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_tsep_1(sK5,sK2)
    | ~ v1_tsep_1(sK4,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_4696])).

cnf(c_6619,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),sK5,sK3) = iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_tsep_1(sK5,sK2) != iProver_top
    | v1_tsep_1(sK4,sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6618])).

cnf(c_6621,plain,
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
    inference(instantiation,[status(thm)],[c_6619])).

cnf(c_33,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_72,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_68,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_42,negated_conjecture,
    ( v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_63,plain,
    ( v1_tsep_1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_45,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_60,plain,
    ( v1_tsep_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26447,c_8646,c_6716,c_6621,c_5161,c_5131,c_73,c_72,c_71,c_70,c_69,c_68,c_67,c_66,c_64,c_63,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_53])).


%------------------------------------------------------------------------------

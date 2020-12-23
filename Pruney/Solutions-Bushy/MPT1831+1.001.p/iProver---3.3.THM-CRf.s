%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1831+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:35 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  249 (3047 expanded)
%              Number of clauses        :  171 ( 636 expanded)
%              Number of leaves         :   15 (1343 expanded)
%              Depth                    :   20
%              Number of atoms          : 2530 (71529 expanded)
%              Number of equality atoms :  636 (1410 expanded)
%              Maximal formula depth    :   26 (  10 average)
%              Maximal clause size      :   52 (   9 average)
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
                 => ( ~ r1_tsep_1(X2,X3)
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
                           => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                   => ( ~ r1_tsep_1(X2,X3)
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
                             => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
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

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7)) )
        & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),sK7))
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
              & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),sK6),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
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
                  & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & ~ r1_tsep_1(X2,X3)
          & m1_pre_topc(X3,X0)
          & v1_tsep_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5)) )
                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,sK5),X4),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,X2,sK5),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK5,X1)
                & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & ~ r1_tsep_1(X2,sK5)
        & m1_pre_topc(sK5,X0)
        & v1_tsep_1(sK5,X0)
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
                      & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & ~ r1_tsep_1(X2,X3)
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
                    & r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,sK4,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK4,X1)
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & ~ r1_tsep_1(sK4,X3)
            & m1_pre_topc(X3,X0)
            & v1_tsep_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & v1_tsep_1(sK4,X0)
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
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
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
                        & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,sK3,X3,k2_tsep_1(X0,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(X5,X3,sK3)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,X2,sK3)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & ~ r1_tsep_1(X2,X3)
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
                            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & ~ r1_tsep_1(X2,X3)
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
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
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

fof(f42,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & ~ r1_tsep_1(sK4,sK5)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f41,f40,f39,f38,f37,f36])).

fof(f92,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f42])).

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
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
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
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
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

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

fof(f51,plain,(
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

fof(f2,axiom,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(cnf_transformation,[],[f11])).

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
    inference(cnf_transformation,[],[f11])).

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
    inference(cnf_transformation,[],[f11])).

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
    inference(cnf_transformation,[],[f15])).

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
    inference(cnf_transformation,[],[f15])).

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

fof(f66,plain,(
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

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
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

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f42])).

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
    inference(definition_folding,[],[f19,f25,f24])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_29,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2137,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3030,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2137])).

cnf(c_25,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | r1_tsep_1(X3,X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,negated_conjecture,
    ( ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_597,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    | sK5 != X0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_38])).

cnf(c_598,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_602,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_44,c_41])).

cnf(c_603,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(renaming,[status(thm)],[c_602])).

cnf(c_2115,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,sK4,k2_tsep_1(X0_56,sK4,sK5),X0_55),k3_tmap_1(X0_56,X1_56,sK5,k2_tsep_1(X0_56,sK4,sK5),X1_55))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)),X1_55)
    | ~ v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56))
    | ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56))
    | ~ m1_pre_topc(sK5,X0_56)
    | ~ m1_pre_topc(sK4,X0_56)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_603])).

cnf(c_3052,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,sK4,k2_tsep_1(X0_56,sK4,sK5),X0_55),k3_tmap_1(X0_56,X1_56,sK5,k2_tsep_1(X0_56,sK4,sK5),X1_55)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)),X1_55) = iProver_top
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
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
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2115])).

cnf(c_5808,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
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
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_3052])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_51,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_52,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_53,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_54,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_55,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_56,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_42,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_59,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_62,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_64,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_65,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_67,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_68,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_69,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_71,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_72,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3664,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,sK4,k2_tsep_1(X0_56,sK4,sK5),X0_55),k3_tmap_1(X0_56,sK3,sK5,k2_tsep_1(X0_56,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)),sK7)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,X0_56)
    | ~ m1_pre_topc(sK4,X0_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2115])).

cnf(c_3665,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,sK4,k2_tsep_1(X0_56,sK4,sK5),X0_55),k3_tmap_1(X0_56,sK3,sK5,k2_tsep_1(X0_56,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK5,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)),sK7) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3664])).

cnf(c_3667,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
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
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3665])).

cnf(c_6349,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5808,c_51,c_52,c_53,c_54,c_55,c_56,c_59,c_62,c_64,c_65,c_67,c_68,c_69,c_71,c_72,c_3667])).

cnf(c_5,plain,
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

cnf(c_2158,plain,
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
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3009,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_56,X1_56,X0_56,X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56)))) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_2136,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3031,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2136])).

cnf(c_9,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2154,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X0_55,X1_55)
    | ~ v1_funct_2(X1_55,X0_54,X1_54)
    | ~ v1_funct_2(X0_55,X0_54,X1_54)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55)
    | X1_55 = X0_55 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3013,plain,
    ( X0_55 = X1_55
    | r2_funct_2(X0_54,X1_54,X1_55,X0_55) != iProver_top
    | v1_funct_2(X1_55,X0_54,X1_54) != iProver_top
    | v1_funct_2(X0_55,X0_54,X1_54) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2154])).

cnf(c_8770,plain,
    ( sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3031,c_3013])).

cnf(c_9244,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8770,c_68,c_69])).

cnf(c_9245,plain,
    ( sK7 = X0_55
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),X0_55,sK7) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_9244])).

cnf(c_10044,plain,
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
    inference(superposition,[status(thm)],[c_3009,c_9245])).

cnf(c_12468,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_10044,c_54,c_55,c_56])).

cnf(c_12469,plain,
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
    inference(renaming,[status(thm)],[c_12468])).

cnf(c_12486,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6349,c_12469])).

cnf(c_57,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_60,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2160,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56)
    | ~ l1_pre_topc(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3726,plain,
    ( ~ m1_pre_topc(X0_56,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0_56,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_3916,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3726])).

cnf(c_3917,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3916])).

cnf(c_2,plain,
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

cnf(c_2161,plain,
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
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3810,plain,
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
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_4444,plain,
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
    inference(instantiation,[status(thm)],[c_3810])).

cnf(c_4813,plain,
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
    inference(instantiation,[status(thm)],[c_4444])).

cnf(c_4814,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4813])).

cnf(c_4816,plain,
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
    inference(instantiation,[status(thm)],[c_4814])).

cnf(c_1,plain,
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

cnf(c_2162,plain,
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
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3820,plain,
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
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_4511,plain,
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
    inference(instantiation,[status(thm)],[c_3820])).

cnf(c_4836,plain,
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
    inference(instantiation,[status(thm)],[c_4511])).

cnf(c_4837,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4836])).

cnf(c_4839,plain,
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
    inference(instantiation,[status(thm)],[c_4837])).

cnf(c_0,plain,
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

cnf(c_2163,plain,
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
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3830,plain,
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
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_4704,plain,
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
    inference(instantiation,[status(thm)],[c_3830])).

cnf(c_6887,plain,
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
    inference(instantiation,[status(thm)],[c_4704])).

cnf(c_6888,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_6887])).

cnf(c_6890,plain,
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
    inference(instantiation,[status(thm)],[c_6888])).

cnf(c_7,plain,
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

cnf(c_2156,plain,
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
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3745,plain,
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
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_4090,plain,
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
    inference(instantiation,[status(thm)],[c_3745])).

cnf(c_8251,plain,
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
    inference(instantiation,[status(thm)],[c_4090])).

cnf(c_8252,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_8251])).

cnf(c_8254,plain,
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
    inference(instantiation,[status(thm)],[c_8252])).

cnf(c_6,plain,
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

cnf(c_2157,plain,
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
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3775,plain,
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
    inference(instantiation,[status(thm)],[c_2157])).

cnf(c_4275,plain,
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
    inference(instantiation,[status(thm)],[c_3775])).

cnf(c_8454,plain,
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
    inference(instantiation,[status(thm)],[c_4275])).

cnf(c_8455,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_8454])).

cnf(c_8457,plain,
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
    inference(instantiation,[status(thm)],[c_8455])).

cnf(c_12736,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12486,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_59,c_60,c_62,c_64,c_65,c_67,c_68,c_69,c_71,c_3917,c_4816,c_4839,c_6890,c_8254,c_8457])).

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
    inference(cnf_transformation,[],[f66])).

cnf(c_2148,plain,
    ( sP0(X0_56,X1_56,X0_55,X2_56,X3_56)
    | ~ v5_pre_topc(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),X1_56,X0_56)
    | ~ v5_pre_topc(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),X2_56,X0_56)
    | ~ v1_funct_2(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),u1_struct_0(X1_56),u1_struct_0(X0_56))
    | ~ v1_funct_2(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),u1_struct_0(X2_56),u1_struct_0(X0_56))
    | ~ m1_subset_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56))))
    | ~ m1_subset_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X0_56))))
    | ~ v1_funct_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55))
    | ~ v1_funct_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3019,plain,
    ( sP0(X0_56,X1_56,X0_55,X2_56,X3_56) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),X1_56,X0_56) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),X2_56,X0_56) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),u1_struct_0(X1_56),u1_struct_0(X0_56)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),u1_struct_0(X2_56),u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X0_56)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X0_56)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X1_56,X0_55)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_56,X0_56,k1_tsep_1(X3_56,X2_56,X1_56),X2_56,X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2148])).

cnf(c_12741,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12736,c_3019])).

cnf(c_26,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_657,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
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
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_658,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_662,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_44,c_41])).

cnf(c_663,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(renaming,[status(thm)],[c_662])).

cnf(c_2114,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,sK4,k2_tsep_1(X0_56,sK4,sK5),X0_55),k3_tmap_1(X0_56,X1_56,sK5,k2_tsep_1(X0_56,sK4,sK5),X1_55))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)),X0_55)
    | ~ v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56))
    | ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56))
    | ~ m1_pre_topc(sK5,X0_56)
    | ~ m1_pre_topc(sK4,X0_56)
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ v1_funct_1(X1_55)
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_663])).

cnf(c_3053,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_56,sK4,sK5)),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,sK4,k2_tsep_1(X0_56,sK4,sK5),X0_55),k3_tmap_1(X0_56,X1_56,sK5,k2_tsep_1(X0_56,sK4,sK5),X1_55)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_56),k3_tmap_1(X0_56,X1_56,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,X1_56,sK4,sK5,X0_55,X1_55)),X0_55) = iProver_top
    | v1_funct_2(X1_55,u1_struct_0(sK5),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(X1_56)) != iProver_top
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
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2114])).

cnf(c_6371,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
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
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_3053])).

cnf(c_3659,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,sK4,k2_tsep_1(X0_56,sK4,sK5),X0_55),k3_tmap_1(X0_56,sK3,sK5,k2_tsep_1(X0_56,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)),X0_55)
    | ~ v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,X0_56)
    | ~ m1_pre_topc(sK4,X0_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_3660,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_56,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,sK4,k2_tsep_1(X0_56,sK4,sK5),X0_55),k3_tmap_1(X0_56,sK3,sK5,k2_tsep_1(X0_56,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(X0_56,sK3,k1_tsep_1(X0_56,sK4,sK5),sK4,k10_tmap_1(X0_56,sK3,sK4,sK5,X0_55,sK7)),X0_55) = iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_56) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3659])).

cnf(c_3662,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
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
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3660])).

cnf(c_6631,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6371,c_51,c_52,c_53,c_54,c_55,c_56,c_59,c_62,c_64,c_65,c_67,c_68,c_69,c_71,c_72,c_3662])).

cnf(c_2132,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_3035,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2132])).

cnf(c_8771,plain,
    ( sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3035,c_3013])).

cnf(c_9285,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8771,c_64,c_65])).

cnf(c_9286,plain,
    ( sK6 = X0_55
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0_55,sK6) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_9285])).

cnf(c_10043,plain,
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
    inference(superposition,[status(thm)],[c_3009,c_9286])).

cnf(c_12447,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_10043,c_54,c_55,c_56])).

cnf(c_12448,plain,
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
    inference(renaming,[status(thm)],[c_12447])).

cnf(c_12465,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6631,c_12448])).

cnf(c_3750,plain,
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
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_4245,plain,
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
    inference(instantiation,[status(thm)],[c_3750])).

cnf(c_8375,plain,
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
    inference(instantiation,[status(thm)],[c_4245])).

cnf(c_8376,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_8375])).

cnf(c_8378,plain,
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
    inference(instantiation,[status(thm)],[c_8376])).

cnf(c_3780,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | v1_funct_2(k3_tmap_1(sK2,X1_56,X0_56,sK4,X0_55),u1_struct_0(sK4),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X0_56,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_2157])).

cnf(c_4309,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))
    | v1_funct_2(k3_tmap_1(sK2,X0_56,k1_tsep_1(sK2,sK4,sK5),sK4,X0_55),u1_struct_0(sK4),u1_struct_0(X0_56))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_56))))
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_56)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_3780])).

cnf(c_8707,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) ),
    inference(instantiation,[status(thm)],[c_4309])).

cnf(c_8708,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_55,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8707])).

cnf(c_8710,plain,
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
    inference(instantiation,[status(thm)],[c_8708])).

cnf(c_12719,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12465,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_59,c_60,c_62,c_64,c_65,c_67,c_68,c_69,c_71,c_3917,c_4816,c_4839,c_6890,c_8378,c_8710])).

cnf(c_12761,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12741,c_12719,c_12736])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2152,plain,
    ( ~ sP1(X0_56,X1_56,X0_55,X2_56,X3_56)
    | ~ sP0(X3_56,X2_56,X0_55,X1_56,X0_56)
    | v5_pre_topc(X0_55,k1_tsep_1(X0_56,X1_56,X2_56),X3_56) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3015,plain,
    ( sP1(X0_56,X1_56,X0_55,X2_56,X3_56) != iProver_top
    | sP0(X3_56,X2_56,X0_55,X1_56,X0_56) != iProver_top
    | v5_pre_topc(X0_55,k1_tsep_1(X0_56,X1_56,X2_56),X3_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2152])).

cnf(c_3004,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | v1_funct_2(X1_55,u1_struct_0(X2_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_56,X1_56,X2_56,X0_56,X1_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_56,X2_56,X0_56)),u1_struct_0(X1_56)))) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2163])).

cnf(c_28,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2138,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3029,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2138])).

cnf(c_73,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5329,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3029,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_59,c_60,c_62,c_64,c_65,c_67,c_68,c_69,c_71,c_73,c_4816,c_4839])).

cnf(c_5330,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5329])).

cnf(c_5335,plain,
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
    inference(superposition,[status(thm)],[c_3004,c_5330])).

cnf(c_5786,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5335,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_59,c_60,c_62,c_64,c_65,c_67,c_68,c_69,c_71])).

cnf(c_7989,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3015,c_5786])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_2139,plain,
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
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3800,plain,
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
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_4394,plain,
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
    inference(instantiation,[status(thm)],[c_3800])).

cnf(c_6698,plain,
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
    inference(instantiation,[status(thm)],[c_4394])).

cnf(c_6699,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_6698])).

cnf(c_6701,plain,
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
    inference(instantiation,[status(thm)],[c_6699])).

cnf(c_31,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_70,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_66,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_40,negated_conjecture,
    ( v1_tsep_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_61,plain,
    ( v1_tsep_1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_58,plain,
    ( v1_tsep_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12761,c_7989,c_6890,c_6701,c_4839,c_4816,c_71,c_70,c_69,c_68,c_67,c_66,c_65,c_64,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_53,c_52,c_51])).


%------------------------------------------------------------------------------

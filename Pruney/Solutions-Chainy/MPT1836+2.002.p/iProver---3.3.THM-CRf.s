%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:28 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  237 (6693 expanded)
%              Number of clauses        :  165 (1220 expanded)
%              Number of leaves         :   14 (3118 expanded)
%              Depth                    :   35
%              Number of atoms          : 2030 (168996 expanded)
%              Number of equality atoms :  755 (10277 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal clause size      :   54 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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

fof(f7,negated_conjecture,(
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
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
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
    inference(negated_conjecture,[],[f6])).

fof(f19,plain,(
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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
          & v1_borsuk_1(X3,X0)
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
        & v1_borsuk_1(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
              & v1_borsuk_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_borsuk_1(X2,X0)
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
            & v1_borsuk_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & v1_borsuk_1(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
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
                & v1_borsuk_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_borsuk_1(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
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
                  & v1_borsuk_1(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & v1_borsuk_1(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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
    & v1_borsuk_1(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & v1_borsuk_1(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f36,f35,f34,f33,f32,f31])).

fof(f83,plain,(
    k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f37])).

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
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f11])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f12])).

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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f15])).

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
    inference(cnf_transformation,[],[f16])).

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
    inference(cnf_transformation,[],[f16])).

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
    inference(cnf_transformation,[],[f16])).

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
    inference(ennf_transformation,[],[f1])).

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

fof(f24,plain,(
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

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,(
    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f21,plain,(
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

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f22,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f27])).

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
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f23,plain,(
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
                  | ~ v1_borsuk_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f18,f22,f21])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_borsuk_1(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_28,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1944,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(subtyping,[status(esa)],[c_28])).

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
    inference(cnf_transformation,[],[f41])).

cnf(c_1967,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5007,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)) = iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1967])).

cnf(c_5667,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_5007])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_50,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_51,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_55,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_40,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_57,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_58,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_60,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5780,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5667,c_49,c_50,c_51,c_55,c_57,c_58,c_60])).

cnf(c_5781,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5780])).

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
    inference(cnf_transformation,[],[f42])).

cnf(c_1968,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5006,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1968])).

cnf(c_5536,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_5006])).

cnf(c_5800,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5536,c_49,c_50,c_51,c_55,c_57,c_58,c_60])).

cnf(c_5801,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5800])).

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
    inference(cnf_transformation,[],[f45])).

cnf(c_1961,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_5013,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_9145,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(sK2,X2_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5801,c_5013])).

cnf(c_11174,plain,
    ( v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(sK2,X2_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9145,c_49,c_50,c_51,c_55,c_57,c_58,c_60,c_5667])).

cnf(c_11175,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(sK2,X2_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
    inference(renaming,[status(thm)],[c_11174])).

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
    inference(cnf_transformation,[],[f46])).

cnf(c_1962,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_5012,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1962])).

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
    inference(cnf_transformation,[],[f47])).

cnf(c_1963,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_5011,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1963])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_27,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_524,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1,c_27])).

cnf(c_525,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK6)
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_527,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_36,c_35,c_33])).

cnf(c_528,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_527])).

cnf(c_1922,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_528])).

cnf(c_5030,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1922])).

cnf(c_5248,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5030,c_1944])).

cnf(c_7533,plain,
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
    inference(superposition,[status(thm)],[c_5011,c_5248])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_52,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_53,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_54,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_61,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_62,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1939,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_5046,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1939])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1943,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_5050,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1943])).

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
    inference(cnf_transformation,[],[f40])).

cnf(c_1966,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5008,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1966])).

cnf(c_5873,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK5,X1_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5050,c_5008])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_65,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_66,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6121,plain,
    ( v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,X1_54) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5873,c_52,c_53,c_54,c_58,c_65,c_66])).

cnf(c_6122,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK5,X1_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6121])).

cnf(c_6138,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5046,c_6122])).

cnf(c_6265,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6138])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1965,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(k1_tsep_1(X1_54,X2_54,X0_54),X1_54)
    | ~ l1_pre_topc(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_5009,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_54,X2_54,X0_54),X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1965])).

cnf(c_6557,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_5009])).

cnf(c_11127,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7533,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,c_60,c_61,c_62,c_6265,c_6557])).

cnf(c_11128,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11127])).

cnf(c_11136,plain,
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
    inference(superposition,[status(thm)],[c_5012,c_11128])).

cnf(c_11560,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11136,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,c_60,c_61,c_62,c_6265,c_6557])).

cnf(c_11561,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11560])).

cnf(c_11568,plain,
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
    inference(superposition,[status(thm)],[c_5801,c_11561])).

cnf(c_64,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_68,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11617,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11568,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_11618,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11617])).

cnf(c_11625,plain,
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
    inference(superposition,[status(thm)],[c_11175,c_11618])).

cnf(c_11820,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11625,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,c_60,c_61,c_62,c_64,c_65,c_66,c_68,c_6265,c_6557])).

cnf(c_11821,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11820])).

cnf(c_11826,plain,
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
    inference(superposition,[status(thm)],[c_5781,c_11821])).

cnf(c_11837,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11826,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_26,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_504,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1,c_26])).

cnf(c_505,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_507,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_32,c_31,c_29])).

cnf(c_508,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_507])).

cnf(c_1923,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_508])).

cnf(c_5029,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1923])).

cnf(c_5239,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5029,c_1944])).

cnf(c_7532,plain,
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
    inference(superposition,[status(thm)],[c_5011,c_5239])).

cnf(c_11048,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7532,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,c_60,c_61,c_62,c_6265,c_6557])).

cnf(c_11049,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11048])).

cnf(c_11057,plain,
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
    inference(superposition,[status(thm)],[c_5012,c_11049])).

cnf(c_11453,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11057,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,c_60,c_61,c_62,c_6265,c_6557])).

cnf(c_11454,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11453])).

cnf(c_11461,plain,
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
    inference(superposition,[status(thm)],[c_5801,c_11454])).

cnf(c_11500,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11461,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_11501,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11500])).

cnf(c_11508,plain,
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
    inference(superposition,[status(thm)],[c_11175,c_11501])).

cnf(c_11680,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11508,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,c_60,c_61,c_62,c_64,c_65,c_66,c_68,c_6265,c_6557])).

cnf(c_11681,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11680])).

cnf(c_11686,plain,
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
    inference(superposition,[status(thm)],[c_5781,c_11681])).

cnf(c_11694,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11686,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_1955,plain,
    ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54)
    | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),X1_54,X0_54)
    | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),X2_54,X0_54)
    | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52))
    | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_5019,plain,
    ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),X1_54,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),X2_54,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_10150,plain,
    ( sP0(X0_54,sK5,X0_52,sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),sK4,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_5019])).

cnf(c_10160,plain,
    ( sP0(X0_54,sK5,X0_52,sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),sK4,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10150,c_1944])).

cnf(c_11700,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11694,c_10160])).

cnf(c_11746,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11700,c_11694])).

cnf(c_30,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_67,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_11774,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11746,c_65,c_66,c_67,c_68])).

cnf(c_11775,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11774])).

cnf(c_11840,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11837,c_11775])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_63,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_12031,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11840,c_61,c_62,c_63,c_64])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1959,plain,
    ( ~ sP1(X0_54,X1_54,X0_52,X2_54,X3_54)
    | ~ sP0(X3_54,X2_54,X0_52,X1_54,X0_54)
    | v5_pre_topc(X0_52,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5015,plain,
    ( sP1(X0_54,X1_54,X0_52,X2_54,X3_54) != iProver_top
    | sP0(X3_54,X2_54,X0_52,X1_54,X0_54) != iProver_top
    | v5_pre_topc(X0_52,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1959])).

cnf(c_7194,plain,
    ( sP1(sK2,sK4,X0_52,sK5,X0_54) != iProver_top
    | sP0(X0_54,sK5,X0_52,sK4,sK2) != iProver_top
    | v5_pre_topc(X0_52,sK2,X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_5015])).

cnf(c_12037,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_12031,c_7194])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_borsuk_1(X3,X0)
    | ~ v1_borsuk_1(X1,X0)
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
    inference(cnf_transformation,[],[f62])).

cnf(c_1946,plain,
    ( sP1(X0_54,X1_54,X0_52,X2_54,X3_54)
    | ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))
    | ~ v1_borsuk_1(X1_54,X0_54)
    | ~ v1_borsuk_1(X2_54,X0_54)
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(X3_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_8667,plain,
    ( sP1(X0_54,sK4,k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_borsuk_1(sK5,X0_54)
    | ~ v1_borsuk_1(sK4,X0_54)
    | ~ m1_pre_topc(sK5,X0_54)
    | ~ m1_pre_topc(sK4,X0_54)
    | ~ m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_8673,plain,
    ( sP1(X0_54,sK4,k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
    | v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_borsuk_1(sK5,X0_54) != iProver_top
    | v1_borsuk_1(sK4,X0_54) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8667])).

cnf(c_8675,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_borsuk_1(sK5,sK2) != iProver_top
    | v1_borsuk_1(sK4,sK2) != iProver_top
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
    inference(instantiation,[status(thm)],[c_8673])).

cnf(c_5672,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7),u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(sK5,X1_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_6476,plain,
    ( v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,X0_54)
    | ~ m1_pre_topc(sK4,X0_54)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5672])).

cnf(c_6477,plain,
    ( v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6476])).

cnf(c_6479,plain,
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
    inference(instantiation,[status(thm)],[c_6477])).

cnf(c_5671,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(sK5,X1_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_6313,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,X0_54)
    | ~ m1_pre_topc(sK4,X0_54)
    | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_5671])).

cnf(c_6314,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6313])).

cnf(c_6316,plain,
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
    inference(instantiation,[status(thm)],[c_6314])).

cnf(c_25,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1945,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_5051,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1945])).

cnf(c_5816,plain,
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
    inference(superposition,[status(thm)],[c_5801,c_5051])).

cnf(c_5824,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5816,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_5825,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5824])).

cnf(c_5831,plain,
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
    inference(superposition,[status(thm)],[c_5781,c_5825])).

cnf(c_5839,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5831,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_38,negated_conjecture,
    ( v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_59,plain,
    ( v1_borsuk_1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,negated_conjecture,
    ( v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_56,plain,
    ( v1_borsuk_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12037,c_8675,c_6479,c_6316,c_6265,c_5839,c_68,c_66,c_65,c_64,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_53,c_52,c_51,c_50,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:12:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.81/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.98  
% 3.81/0.98  ------  iProver source info
% 3.81/0.98  
% 3.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.98  git: non_committed_changes: false
% 3.81/0.98  git: last_make_outside_of_git: false
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  ------ Parsing...
% 3.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  ------ Proving...
% 3.81/0.98  ------ Problem Properties 
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  clauses                                 47
% 3.81/0.98  conjectures                             22
% 3.81/0.98  EPR                                     17
% 3.81/0.98  Horn                                    38
% 3.81/0.98  unary                                   21
% 3.81/0.98  binary                                  8
% 3.81/0.98  lits                                    193
% 3.81/0.98  lits eq                                 3
% 3.81/0.98  fd_pure                                 0
% 3.81/0.98  fd_pseudo                               0
% 3.81/0.98  fd_cond                                 0
% 3.81/0.98  fd_pseudo_cond                          0
% 3.81/0.98  AC symbols                              0
% 3.81/0.98  
% 3.81/0.98  ------ Input Options Time Limit: Unbounded
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.81/0.98  Current options:
% 3.81/0.98  ------ 
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 33 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 40 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 45 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 45 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  % SZS status Theorem for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  fof(f6,conjecture,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f7,negated_conjecture,(
% 3.81/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 3.81/0.98    inference(negated_conjecture,[],[f6])).
% 3.81/0.98  
% 3.81/0.98  fof(f19,plain,(
% 3.81/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f7])).
% 3.81/0.98  
% 3.81/0.98  fof(f20,plain,(
% 3.81/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f19])).
% 3.81/0.98  
% 3.81/0.98  fof(f36,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),sK7) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK7,X3,X1) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f35,plain,(
% 3.81/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),sK6) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK6,X2,X1) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f34,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5))) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X4) & k1_tsep_1(X0,X2,sK5) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(X5,sK5,X1) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & v1_borsuk_1(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f33,plain,(
% 3.81/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X4) & k1_tsep_1(X0,sK4,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(X4,sK4,X1) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & v1_borsuk_1(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f32,plain,(
% 3.81/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),X0,sK3) | ~v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f31,plain,(
% 3.81/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(sK2,X2,X3) = sK2 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_borsuk_1(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f37,plain,(
% 3.81/0.98    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) & k1_tsep_1(sK2,sK4,sK5) = sK2 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & v1_borsuk_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & v1_borsuk_1(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f36,f35,f34,f33,f32,f31])).
% 3.81/0.98  
% 3.81/0.98  fof(f83,plain,(
% 3.81/0.98    k1_tsep_1(sK2,sK4,sK5) = sK2),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f2,axiom,(
% 3.81/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f11,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f2])).
% 3.81/0.98  
% 3.81/0.98  fof(f12,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f11])).
% 3.81/0.98  
% 3.81/0.98  fof(f41,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f12])).
% 3.81/0.98  
% 3.81/0.98  fof(f63,plain,(
% 3.81/0.98    ~v2_struct_0(sK2)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f64,plain,(
% 3.81/0.98    v2_pre_topc(sK2)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f65,plain,(
% 3.81/0.98    l1_pre_topc(sK2)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f69,plain,(
% 3.81/0.98    ~v2_struct_0(sK4)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f71,plain,(
% 3.81/0.98    m1_pre_topc(sK4,sK2)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f72,plain,(
% 3.81/0.98    ~v2_struct_0(sK5)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f74,plain,(
% 3.81/0.98    m1_pre_topc(sK5,sK2)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f42,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f12])).
% 3.81/0.98  
% 3.81/0.98  fof(f4,axiom,(
% 3.81/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f15,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f4])).
% 3.81/0.98  
% 3.81/0.98  fof(f16,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f15])).
% 3.81/0.98  
% 3.81/0.98  fof(f45,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f16])).
% 3.81/0.98  
% 3.81/0.98  fof(f46,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f16])).
% 3.81/0.98  
% 3.81/0.98  fof(f47,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f16])).
% 3.81/0.98  
% 3.81/0.98  fof(f1,axiom,(
% 3.81/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f9,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.81/0.98    inference(ennf_transformation,[],[f1])).
% 3.81/0.98  
% 3.81/0.98  fof(f10,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.81/0.98    inference(flattening,[],[f9])).
% 3.81/0.98  
% 3.81/0.98  fof(f24,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.81/0.98    inference(nnf_transformation,[],[f10])).
% 3.81/0.98  
% 3.81/0.98  fof(f38,plain,(
% 3.81/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f24])).
% 3.81/0.98  
% 3.81/0.98  fof(f84,plain,(
% 3.81/0.98    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f75,plain,(
% 3.81/0.98    v1_funct_1(sK6)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f76,plain,(
% 3.81/0.98    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f78,plain,(
% 3.81/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f66,plain,(
% 3.81/0.98    ~v2_struct_0(sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f67,plain,(
% 3.81/0.98    v2_pre_topc(sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f68,plain,(
% 3.81/0.98    l1_pre_topc(sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f82,plain,(
% 3.81/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f40,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f12])).
% 3.81/0.98  
% 3.81/0.98  fof(f79,plain,(
% 3.81/0.98    v1_funct_1(sK7)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f80,plain,(
% 3.81/0.98    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f3,axiom,(
% 3.81/0.98    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f8,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.81/0.98    inference(pure_predicate_removal,[],[f3])).
% 3.81/0.98  
% 3.81/0.98  fof(f13,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f8])).
% 3.81/0.98  
% 3.81/0.98  fof(f14,plain,(
% 3.81/0.98    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f13])).
% 3.81/0.98  
% 3.81/0.98  fof(f44,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f14])).
% 3.81/0.98  
% 3.81/0.98  fof(f85,plain,(
% 3.81/0.98    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f21,plain,(
% 3.81/0.98    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 3.81/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.81/0.98  
% 3.81/0.98  fof(f28,plain,(
% 3.81/0.98    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.81/0.98    inference(nnf_transformation,[],[f21])).
% 3.81/0.98  
% 3.81/0.98  fof(f29,plain,(
% 3.81/0.98    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.81/0.98    inference(flattening,[],[f28])).
% 3.81/0.98  
% 3.81/0.98  fof(f30,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.81/0.98    inference(rectify,[],[f29])).
% 3.81/0.98  
% 3.81/0.98  fof(f61,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 3.81/0.98    inference(cnf_transformation,[],[f30])).
% 3.81/0.98  
% 3.81/0.98  fof(f81,plain,(
% 3.81/0.98    v5_pre_topc(sK7,sK5,sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f77,plain,(
% 3.81/0.98    v5_pre_topc(sK6,sK4,sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f22,plain,(
% 3.81/0.98    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 3.81/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.81/0.98  
% 3.81/0.98  fof(f25,plain,(
% 3.81/0.98    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.81/0.98    inference(nnf_transformation,[],[f22])).
% 3.81/0.98  
% 3.81/0.98  fof(f26,plain,(
% 3.81/0.98    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.81/0.98    inference(flattening,[],[f25])).
% 3.81/0.98  
% 3.81/0.98  fof(f27,plain,(
% 3.81/0.98    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 3.81/0.98    inference(rectify,[],[f26])).
% 3.81/0.98  
% 3.81/0.98  fof(f51,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f27])).
% 3.81/0.98  
% 3.81/0.98  fof(f5,axiom,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))))))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f17,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f5])).
% 3.81/0.98  
% 3.81/0.98  fof(f18,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f17])).
% 3.81/0.98  
% 3.81/0.98  fof(f23,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(definition_folding,[],[f18,f22,f21])).
% 3.81/0.98  
% 3.81/0.98  fof(f62,plain,(
% 3.81/0.98    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f23])).
% 3.81/0.98  
% 3.81/0.98  fof(f86,plain,(
% 3.81/0.98    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f73,plain,(
% 3.81/0.98    v1_borsuk_1(sK5,sK2)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f70,plain,(
% 3.81/0.98    v1_borsuk_1(sK4,sK2)),
% 3.81/0.98    inference(cnf_transformation,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  cnf(c_28,negated_conjecture,
% 3.81/0.98      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 3.81/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1944,negated_conjecture,
% 3.81/0.98      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_28]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.81/0.98      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 3.81/0.98      | ~ m1_pre_topc(X1,X5)
% 3.81/0.98      | ~ m1_pre_topc(X4,X5)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.81/0.98      | ~ v2_pre_topc(X2)
% 3.81/0.98      | ~ v2_pre_topc(X5)
% 3.81/0.98      | ~ l1_pre_topc(X2)
% 3.81/0.98      | ~ l1_pre_topc(X5)
% 3.81/0.98      | v2_struct_0(X5)
% 3.81/0.98      | v2_struct_0(X2)
% 3.81/0.98      | v2_struct_0(X4)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_funct_1(X3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1967,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.81/0.98      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 3.81/0.98      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))
% 3.81/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 3.81/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 3.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ v2_pre_topc(X3_54)
% 3.81/0.98      | ~ v2_pre_topc(X1_54)
% 3.81/0.98      | ~ l1_pre_topc(X3_54)
% 3.81/0.98      | ~ l1_pre_topc(X1_54)
% 3.81/0.98      | v2_struct_0(X0_54)
% 3.81/0.98      | v2_struct_0(X1_54)
% 3.81/0.98      | v2_struct_0(X3_54)
% 3.81/0.98      | v2_struct_0(X2_54)
% 3.81/0.98      | ~ v1_funct_1(X0_52)
% 3.81/0.98      | ~ v1_funct_1(X1_52) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5007,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)) = iProver_top
% 3.81/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X3_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1967]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5667,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
% 3.81/0.98      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(sK5) = iProver_top
% 3.81/0.98      | v2_struct_0(sK4) = iProver_top
% 3.81/0.98      | v2_struct_0(sK2) = iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_1944,c_5007]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_48,negated_conjecture,
% 3.81/0.98      ( ~ v2_struct_0(sK2) ),
% 3.81/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_49,plain,
% 3.81/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_47,negated_conjecture,
% 3.81/0.98      ( v2_pre_topc(sK2) ),
% 3.81/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_50,plain,
% 3.81/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_46,negated_conjecture,
% 3.81/0.98      ( l1_pre_topc(sK2) ),
% 3.81/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_51,plain,
% 3.81/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_42,negated_conjecture,
% 3.81/0.98      ( ~ v2_struct_0(sK4) ),
% 3.81/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_55,plain,
% 3.81/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_40,negated_conjecture,
% 3.81/0.98      ( m1_pre_topc(sK4,sK2) ),
% 3.81/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_57,plain,
% 3.81/0.98      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_39,negated_conjecture,
% 3.81/0.98      ( ~ v2_struct_0(sK5) ),
% 3.81/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_58,plain,
% 3.81/0.98      ( v2_struct_0(sK5) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_37,negated_conjecture,
% 3.81/0.98      ( m1_pre_topc(sK5,sK2) ),
% 3.81/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_60,plain,
% 3.81/0.98      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5780,plain,
% 3.81/0.98      ( v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_5667,c_49,c_50,c_51,c_55,c_57,c_58,c_60]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5781,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_5780]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.81/0.98      | ~ m1_pre_topc(X1,X5)
% 3.81/0.98      | ~ m1_pre_topc(X4,X5)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.81/0.98      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 3.81/0.98      | ~ v2_pre_topc(X2)
% 3.81/0.98      | ~ v2_pre_topc(X5)
% 3.81/0.98      | ~ l1_pre_topc(X2)
% 3.81/0.98      | ~ l1_pre_topc(X5)
% 3.81/0.98      | v2_struct_0(X5)
% 3.81/0.98      | v2_struct_0(X2)
% 3.81/0.98      | v2_struct_0(X4)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_funct_1(X3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1968,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.81/0.98      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 3.81/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 3.81/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 3.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 3.81/0.98      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ v2_pre_topc(X3_54)
% 3.81/0.98      | ~ v2_pre_topc(X1_54)
% 3.81/0.98      | ~ l1_pre_topc(X3_54)
% 3.81/0.98      | ~ l1_pre_topc(X1_54)
% 3.81/0.98      | v2_struct_0(X0_54)
% 3.81/0.98      | v2_struct_0(X1_54)
% 3.81/0.98      | v2_struct_0(X3_54)
% 3.81/0.98      | v2_struct_0(X2_54)
% 3.81/0.98      | ~ v1_funct_1(X0_52)
% 3.81/0.98      | ~ v1_funct_1(X1_52) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5006,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)))) = iProver_top
% 3.81/0.98      | v2_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X3_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1968]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5536,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(sK5) = iProver_top
% 3.81/0.98      | v2_struct_0(sK4) = iProver_top
% 3.81/0.98      | v2_struct_0(sK2) = iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_1944,c_5006]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5800,plain,
% 3.81/0.98      ( v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_5536,c_49,c_50,c_51,c_55,c_57,c_58,c_60]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5801,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_5800]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_9,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.81/0.98      | ~ m1_pre_topc(X3,X4)
% 3.81/0.98      | ~ m1_pre_topc(X1,X4)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.98      | ~ v2_pre_topc(X2)
% 3.81/0.98      | ~ v2_pre_topc(X4)
% 3.81/0.98      | ~ l1_pre_topc(X2)
% 3.81/0.98      | ~ l1_pre_topc(X4)
% 3.81/0.98      | v2_struct_0(X4)
% 3.81/0.98      | v2_struct_0(X2)
% 3.81/0.98      | ~ v1_funct_1(X0)
% 3.81/0.98      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1961,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.81/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 3.81/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 3.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ v2_pre_topc(X3_54)
% 3.81/0.98      | ~ v2_pre_topc(X1_54)
% 3.81/0.98      | ~ l1_pre_topc(X3_54)
% 3.81/0.98      | ~ l1_pre_topc(X1_54)
% 3.81/0.98      | v2_struct_0(X1_54)
% 3.81/0.98      | v2_struct_0(X3_54)
% 3.81/0.98      | ~ v1_funct_1(X0_52)
% 3.81/0.98      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5013,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X3_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1961]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_9145,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2,X2_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X2_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X2_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_5801,c_5013]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11174,plain,
% 3.81/0.98      ( v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2,X2_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X2_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X2_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_9145,c_49,c_50,c_51,c_55,c_57,c_58,c_60,c_5667]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11175,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2,X2_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X2_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X2_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_11174]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_8,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.81/0.98      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.81/0.98      | ~ m1_pre_topc(X4,X3)
% 3.81/0.98      | ~ m1_pre_topc(X1,X3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.98      | ~ v2_pre_topc(X2)
% 3.81/0.98      | ~ v2_pre_topc(X3)
% 3.81/0.98      | ~ l1_pre_topc(X2)
% 3.81/0.98      | ~ l1_pre_topc(X3)
% 3.81/0.98      | v2_struct_0(X3)
% 3.81/0.98      | v2_struct_0(X2)
% 3.81/0.98      | ~ v1_funct_1(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1962,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.81/0.98      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54))
% 3.81/0.98      | ~ m1_pre_topc(X3_54,X2_54)
% 3.81/0.98      | ~ m1_pre_topc(X0_54,X2_54)
% 3.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ v2_pre_topc(X2_54)
% 3.81/0.98      | ~ v2_pre_topc(X1_54)
% 3.81/0.98      | ~ l1_pre_topc(X2_54)
% 3.81/0.98      | ~ l1_pre_topc(X1_54)
% 3.81/0.98      | v2_struct_0(X1_54)
% 3.81/0.98      | v2_struct_0(X2_54)
% 3.81/0.98      | ~ v1_funct_1(X0_52) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5012,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X2_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X2_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1962]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.81/0.98      | ~ m1_pre_topc(X3,X4)
% 3.81/0.98      | ~ m1_pre_topc(X1,X4)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.98      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.81/0.98      | ~ v2_pre_topc(X2)
% 3.81/0.98      | ~ v2_pre_topc(X4)
% 3.81/0.98      | ~ l1_pre_topc(X2)
% 3.81/0.98      | ~ l1_pre_topc(X4)
% 3.81/0.98      | v2_struct_0(X4)
% 3.81/0.98      | v2_struct_0(X2)
% 3.81/0.98      | ~ v1_funct_1(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1963,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.81/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 3.81/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 3.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.81/0.98      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ v2_pre_topc(X3_54)
% 3.81/0.98      | ~ v2_pre_topc(X1_54)
% 3.81/0.98      | ~ l1_pre_topc(X3_54)
% 3.81/0.98      | ~ l1_pre_topc(X1_54)
% 3.81/0.98      | v2_struct_0(X1_54)
% 3.81/0.98      | v2_struct_0(X3_54)
% 3.81/0.98      | ~ v1_funct_1(X0_52) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5011,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 3.81/0.98      | v2_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X3_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1963]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1,plain,
% 3.81/0.98      ( ~ r2_funct_2(X0,X1,X2,X3)
% 3.81/0.98      | ~ v1_funct_2(X3,X0,X1)
% 3.81/0.98      | ~ v1_funct_2(X2,X0,X1)
% 3.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.81/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.81/0.98      | ~ v1_funct_1(X3)
% 3.81/0.98      | ~ v1_funct_1(X2)
% 3.81/0.98      | X2 = X3 ),
% 3.81/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_27,negated_conjecture,
% 3.81/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
% 3.81/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_524,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.81/0.98      | ~ v1_funct_2(X3,X1,X2)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.98      | ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_funct_1(X3)
% 3.81/0.98      | X3 = X0
% 3.81/0.98      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 3.81/0.98      | u1_struct_0(sK4) != X1
% 3.81/0.98      | u1_struct_0(sK3) != X2
% 3.81/0.98      | sK6 != X3 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_27]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_525,plain,
% 3.81/0.98      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.81/0.98      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 3.81/0.98      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.81/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.81/0.98      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.81/0.98      | ~ v1_funct_1(sK6)
% 3.81/0.98      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_524]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_36,negated_conjecture,
% 3.81/0.98      ( v1_funct_1(sK6) ),
% 3.81/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_35,negated_conjecture,
% 3.81/0.98      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_33,negated_conjecture,
% 3.81/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.81/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_527,plain,
% 3.81/0.98      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.81/0.98      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.81/0.98      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.81/0.98      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_525,c_36,c_35,c_33]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_528,plain,
% 3.81/0.98      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.81/0.98      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.81/0.98      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.81/0.98      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_527]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1922,plain,
% 3.81/0.98      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.81/0.98      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.81/0.98      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.81/0.98      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_528]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5030,plain,
% 3.81/0.98      ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 3.81/0.98      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1922]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5248,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(light_normalisation,[status(thm)],[c_5030,c_1944]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7533,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.98      | v2_struct_0(sK3) = iProver_top
% 3.81/0.98      | v2_struct_0(sK2) = iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_5011,c_5248]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_45,negated_conjecture,
% 3.81/0.98      ( ~ v2_struct_0(sK3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_52,plain,
% 3.81/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_44,negated_conjecture,
% 3.81/0.98      ( v2_pre_topc(sK3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_53,plain,
% 3.81/0.98      ( v2_pre_topc(sK3) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_43,negated_conjecture,
% 3.81/0.98      ( l1_pre_topc(sK3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_54,plain,
% 3.81/0.98      ( l1_pre_topc(sK3) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_61,plain,
% 3.81/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_62,plain,
% 3.81/0.98      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1939,negated_conjecture,
% 3.81/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_33]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5046,plain,
% 3.81/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1939]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_29,negated_conjecture,
% 3.81/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.81/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1943,negated_conjecture,
% 3.81/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_29]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5050,plain,
% 3.81/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1943]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.81/0.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.81/0.98      | ~ m1_pre_topc(X1,X5)
% 3.81/0.98      | ~ m1_pre_topc(X4,X5)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.81/0.98      | ~ v2_pre_topc(X2)
% 3.81/0.98      | ~ v2_pre_topc(X5)
% 3.81/0.98      | ~ l1_pre_topc(X2)
% 3.81/0.98      | ~ l1_pre_topc(X5)
% 3.81/0.98      | v2_struct_0(X5)
% 3.81/0.98      | v2_struct_0(X2)
% 3.81/0.98      | v2_struct_0(X4)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_funct_1(X3)
% 3.81/0.98      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1966,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.81/0.98      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 3.81/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 3.81/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 3.81/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 3.81/0.98      | ~ v2_pre_topc(X3_54)
% 3.81/0.98      | ~ v2_pre_topc(X1_54)
% 3.81/0.98      | ~ l1_pre_topc(X3_54)
% 3.81/0.98      | ~ l1_pre_topc(X1_54)
% 3.81/0.98      | v2_struct_0(X0_54)
% 3.81/0.98      | v2_struct_0(X1_54)
% 3.81/0.98      | v2_struct_0(X3_54)
% 3.81/0.98      | v2_struct_0(X2_54)
% 3.81/0.98      | ~ v1_funct_1(X0_52)
% 3.81/0.98      | ~ v1_funct_1(X1_52)
% 3.81/0.98      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52)) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5008,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X3_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X3_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X2_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(X1_52) != iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52)) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1966]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5873,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK5,X1_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(sK5) = iProver_top
% 3.81/0.98      | v2_struct_0(sK3) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top
% 3.81/0.98      | v1_funct_1(sK7) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_5050,c_5008]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_32,negated_conjecture,
% 3.81/0.98      ( v1_funct_1(sK7) ),
% 3.81/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_65,plain,
% 3.81/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_31,negated_conjecture,
% 3.81/0.98      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.81/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_66,plain,
% 3.81/0.98      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6121,plain,
% 3.81/0.98      ( v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK5,X1_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.81/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_5873,c_52,c_53,c_54,c_58,c_65,c_66]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6122,plain,
% 3.81/0.98      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK5,X1_54) != iProver_top
% 3.81/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_6121]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6138,plain,
% 3.81/0.98      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK5,X0_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK4,X0_54) != iProver_top
% 3.81/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(sK4) = iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 3.81/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_5046,c_6122]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6265,plain,
% 3.81/0.98      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.98      | v2_struct_0(sK4) = iProver_top
% 3.81/0.98      | v2_struct_0(sK2) = iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 3.81/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_6138]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.98      | ~ m1_pre_topc(X2,X1)
% 3.81/0.98      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v2_struct_0(X2)
% 3.81/0.98      | v2_struct_0(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1965,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.81/0.98      | ~ m1_pre_topc(X2_54,X1_54)
% 3.81/0.98      | m1_pre_topc(k1_tsep_1(X1_54,X2_54,X0_54),X1_54)
% 3.81/0.98      | ~ l1_pre_topc(X1_54)
% 3.81/0.98      | v2_struct_0(X0_54)
% 3.81/0.98      | v2_struct_0(X1_54)
% 3.81/0.98      | v2_struct_0(X2_54) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5009,plain,
% 3.81/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.81/0.98      | m1_pre_topc(k1_tsep_1(X1_54,X2_54,X0_54),X1_54) = iProver_top
% 3.81/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.81/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.81/0.98      | v2_struct_0(X2_54) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1965]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6557,plain,
% 3.81/0.98      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2,sK2) = iProver_top
% 3.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.98      | v2_struct_0(sK5) = iProver_top
% 3.81/0.98      | v2_struct_0(sK4) = iProver_top
% 3.81/0.98      | v2_struct_0(sK2) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_1944,c_5009]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11127,plain,
% 3.81/0.98      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_7533,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,
% 3.81/0.98                 c_60,c_61,c_62,c_6265,c_6557]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11128,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_11127]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11136,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.98      | v2_struct_0(sK3) = iProver_top
% 3.81/0.98      | v2_struct_0(sK2) = iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_5012,c_11128]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11560,plain,
% 3.81/0.98      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_11136,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,
% 3.81/0.98                 c_60,c_61,c_62,c_6265,c_6557]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11561,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_11560]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11568,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.98      | v2_struct_0(sK3) = iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.81/0.98      | v1_funct_1(sK7) != iProver_top
% 3.81/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_5801,c_11561]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_64,plain,
% 3.81/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_68,plain,
% 3.81/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11617,plain,
% 3.81/0.98      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_11568,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11618,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_11617]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11625,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.81/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.98      | v2_struct_0(sK3) = iProver_top
% 3.81/0.98      | v2_struct_0(sK2) = iProver_top
% 3.81/0.98      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.81/0.98      | v1_funct_1(sK7) != iProver_top
% 3.81/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_11175,c_11618]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11820,plain,
% 3.81/0.98      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_11625,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,
% 3.81/0.98                 c_60,c_61,c_62,c_64,c_65,c_66,c_68,c_6265,c_6557]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11821,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_11820]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11826,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.81/0.98      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.98      | v2_struct_0(sK3) = iProver_top
% 3.81/0.98      | v1_funct_1(sK7) != iProver_top
% 3.81/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_5781,c_11821]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11837,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_11826,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_26,negated_conjecture,
% 3.81/0.98      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
% 3.81/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_504,plain,
% 3.81/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.81/0.98      | ~ v1_funct_2(X3,X1,X2)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.98      | ~ v1_funct_1(X0)
% 3.81/0.98      | ~ v1_funct_1(X3)
% 3.81/0.98      | X3 = X0
% 3.81/0.98      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 3.81/0.98      | u1_struct_0(sK5) != X1
% 3.81/0.98      | u1_struct_0(sK3) != X2
% 3.81/0.98      | sK7 != X3 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_26]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_505,plain,
% 3.81/0.98      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.98      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.98      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.98      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.81/0.98      | ~ v1_funct_1(sK7)
% 3.81/0.98      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_504]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_507,plain,
% 3.81/0.98      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.81/0.98      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.98      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.98      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_505,c_32,c_31,c_29]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_508,plain,
% 3.81/0.98      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.98      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.98      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.81/0.98      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_507]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1923,plain,
% 3.81/0.98      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.98      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.98      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.81/0.98      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.98      inference(subtyping,[status(esa)],[c_508]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5029,plain,
% 3.81/0.98      ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 3.81/0.98      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1923]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5239,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.98      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.98      inference(light_normalisation,[status(thm)],[c_5029,c_1944]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7532,plain,
% 3.81/0.98      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.98      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.81/0.98      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.98      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v2_struct_0(sK2) = iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_5011,c_5239]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11048,plain,
% 3.81/0.99      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_7532,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,
% 3.81/0.99                 c_60,c_61,c_62,c_6265,c_6557]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11049,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_11048]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11057,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.81/0.99      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v2_struct_0(sK2) = iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_5012,c_11049]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11453,plain,
% 3.81/0.99      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_11057,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,
% 3.81/0.99                 c_60,c_61,c_62,c_6265,c_6557]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11454,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_11453]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11461,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_5801,c_11454]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11500,plain,
% 3.81/0.99      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_11461,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11501,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_11500]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11508,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v2_struct_0(sK2) = iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_11175,c_11501]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11680,plain,
% 3.81/0.99      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_11508,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_58,
% 3.81/0.99                 c_60,c_61,c_62,c_64,c_65,c_66,c_68,c_6265,c_6557]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11681,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_11680]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11686,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.81/0.99      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_5781,c_11681]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11694,plain,
% 3.81/0.99      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_11686,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_15,plain,
% 3.81/0.99      ( sP0(X0,X1,X2,X3,X4)
% 3.81/0.99      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 3.81/0.99      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 3.81/0.99      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 3.81/0.99      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 3.81/0.99      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 3.81/0.99      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 3.81/0.99      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 3.81/0.99      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 3.81/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1955,plain,
% 3.81/0.99      ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54)
% 3.81/0.99      | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),X1_54,X0_54)
% 3.81/0.99      | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),X2_54,X0_54)
% 3.81/0.99      | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),u1_struct_0(X1_54),u1_struct_0(X0_54))
% 3.81/0.99      | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54))
% 3.81/0.99      | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
% 3.81/0.99      | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
% 3.81/0.99      | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52))
% 3.81/0.99      | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52)) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5019,plain,
% 3.81/0.99      ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54) = iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),X1_54,X0_54) != iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),X2_54,X0_54) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52)) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52)) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_10150,plain,
% 3.81/0.99      ( sP0(X0_54,sK5,X0_52,sK4,sK2) = iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),sK5,X0_54) != iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),sK4,X0_54) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52)) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52)) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1944,c_5019]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_10160,plain,
% 3.81/0.99      ( sP0(X0_54,sK5,X0_52,sK4,sK2) = iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),sK5,X0_54) != iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),sK4,X0_54) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52)) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52)) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_10150,c_1944]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11700,plain,
% 3.81/0.99      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_11694,c_10160]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11746,plain,
% 3.81/0.99      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.81/0.99      | v5_pre_topc(sK7,sK5,sK3) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_11700,c_11694]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_30,negated_conjecture,
% 3.81/0.99      ( v5_pre_topc(sK7,sK5,sK3) ),
% 3.81/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_67,plain,
% 3.81/0.99      ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11774,plain,
% 3.81/0.99      ( v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_11746,c_65,c_66,c_67,c_68]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11775,plain,
% 3.81/0.99      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.81/0.99      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.81/0.99      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_11774]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11840,plain,
% 3.81/0.99      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 3.81/0.99      | v5_pre_topc(sK6,sK4,sK3) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(demodulation,[status(thm)],[c_11837,c_11775]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_34,negated_conjecture,
% 3.81/0.99      ( v5_pre_topc(sK6,sK4,sK3) ),
% 3.81/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_63,plain,
% 3.81/0.99      ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_12031,plain,
% 3.81/0.99      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_11840,c_61,c_62,c_63,c_64]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_11,plain,
% 3.81/0.99      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.81/0.99      | ~ sP0(X4,X3,X2,X1,X0)
% 3.81/0.99      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 3.81/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1959,plain,
% 3.81/0.99      ( ~ sP1(X0_54,X1_54,X0_52,X2_54,X3_54)
% 3.81/0.99      | ~ sP0(X3_54,X2_54,X0_52,X1_54,X0_54)
% 3.81/0.99      | v5_pre_topc(X0_52,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5015,plain,
% 3.81/0.99      ( sP1(X0_54,X1_54,X0_52,X2_54,X3_54) != iProver_top
% 3.81/0.99      | sP0(X3_54,X2_54,X0_52,X1_54,X0_54) != iProver_top
% 3.81/0.99      | v5_pre_topc(X0_52,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1959]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_7194,plain,
% 3.81/0.99      ( sP1(sK2,sK4,X0_52,sK5,X0_54) != iProver_top
% 3.81/0.99      | sP0(X0_54,sK5,X0_52,sK4,sK2) != iProver_top
% 3.81/0.99      | v5_pre_topc(X0_52,sK2,X0_54) = iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1944,c_5015]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_12037,plain,
% 3.81/0.99      ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
% 3.81/0.99      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_12031,c_7194]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_24,plain,
% 3.81/0.99      ( sP1(X0,X1,X2,X3,X4)
% 3.81/0.99      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.81/0.99      | ~ v1_borsuk_1(X3,X0)
% 3.81/0.99      | ~ v1_borsuk_1(X1,X0)
% 3.81/0.99      | ~ m1_pre_topc(X3,X0)
% 3.81/0.99      | ~ m1_pre_topc(X1,X0)
% 3.81/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.81/0.99      | ~ v2_pre_topc(X4)
% 3.81/0.99      | ~ v2_pre_topc(X0)
% 3.81/0.99      | ~ l1_pre_topc(X4)
% 3.81/0.99      | ~ l1_pre_topc(X0)
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | v2_struct_0(X4)
% 3.81/0.99      | v2_struct_0(X1)
% 3.81/0.99      | v2_struct_0(X3)
% 3.81/0.99      | ~ v1_funct_1(X2) ),
% 3.81/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1946,plain,
% 3.81/0.99      ( sP1(X0_54,X1_54,X0_52,X2_54,X3_54)
% 3.81/0.99      | ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))
% 3.81/0.99      | ~ v1_borsuk_1(X1_54,X0_54)
% 3.81/0.99      | ~ v1_borsuk_1(X2_54,X0_54)
% 3.81/0.99      | ~ m1_pre_topc(X1_54,X0_54)
% 3.81/0.99      | ~ m1_pre_topc(X2_54,X0_54)
% 3.81/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))))
% 3.81/0.99      | ~ v2_pre_topc(X0_54)
% 3.81/0.99      | ~ v2_pre_topc(X3_54)
% 3.81/0.99      | ~ l1_pre_topc(X0_54)
% 3.81/0.99      | ~ l1_pre_topc(X3_54)
% 3.81/0.99      | v2_struct_0(X0_54)
% 3.81/0.99      | v2_struct_0(X1_54)
% 3.81/0.99      | v2_struct_0(X3_54)
% 3.81/0.99      | v2_struct_0(X2_54)
% 3.81/0.99      | ~ v1_funct_1(X0_52) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_8667,plain,
% 3.81/0.99      ( sP1(X0_54,sK4,k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
% 3.81/0.99      | ~ v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))
% 3.81/0.99      | ~ v1_borsuk_1(sK5,X0_54)
% 3.81/0.99      | ~ v1_borsuk_1(sK4,X0_54)
% 3.81/0.99      | ~ m1_pre_topc(sK5,X0_54)
% 3.81/0.99      | ~ m1_pre_topc(sK4,X0_54)
% 3.81/0.99      | ~ m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))))
% 3.81/0.99      | ~ v2_pre_topc(X0_54)
% 3.81/0.99      | ~ v2_pre_topc(sK3)
% 3.81/0.99      | ~ l1_pre_topc(X0_54)
% 3.81/0.99      | ~ l1_pre_topc(sK3)
% 3.81/0.99      | v2_struct_0(X0_54)
% 3.81/0.99      | v2_struct_0(sK5)
% 3.81/0.99      | v2_struct_0(sK4)
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_1946]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_8673,plain,
% 3.81/0.99      ( sP1(X0_54,sK4,k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
% 3.81/0.99      | v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_borsuk_1(sK5,X0_54) != iProver_top
% 3.81/0.99      | v1_borsuk_1(sK4,X0_54) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK5,X0_54) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK4,X0_54) != iProver_top
% 3.81/0.99      | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.99      | v2_struct_0(sK5) = iProver_top
% 3.81/0.99      | v2_struct_0(sK4) = iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_8667]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_8675,plain,
% 3.81/0.99      ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_borsuk_1(sK5,sK2) != iProver_top
% 3.81/0.99      | v1_borsuk_1(sK4,sK2) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.99      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.99      | v2_struct_0(sK5) = iProver_top
% 3.81/0.99      | v2_struct_0(sK4) = iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v2_struct_0(sK2) = iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_8673]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5672,plain,
% 3.81/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3))
% 3.81/0.99      | v1_funct_2(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7),u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))
% 3.81/0.99      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.99      | ~ m1_pre_topc(X0_54,X1_54)
% 3.81/0.99      | ~ m1_pre_topc(sK5,X1_54)
% 3.81/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 3.81/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.99      | ~ v2_pre_topc(X1_54)
% 3.81/0.99      | ~ v2_pre_topc(sK3)
% 3.81/0.99      | ~ l1_pre_topc(X1_54)
% 3.81/0.99      | ~ l1_pre_topc(sK3)
% 3.81/0.99      | v2_struct_0(X0_54)
% 3.81/0.99      | v2_struct_0(X1_54)
% 3.81/0.99      | v2_struct_0(sK5)
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ v1_funct_1(X0_52)
% 3.81/0.99      | ~ v1_funct_1(sK7) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_1967]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6476,plain,
% 3.81/0.99      ( v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))
% 3.81/0.99      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.99      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 3.81/0.99      | ~ m1_pre_topc(sK5,X0_54)
% 3.81/0.99      | ~ m1_pre_topc(sK4,X0_54)
% 3.81/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.81/0.99      | ~ v2_pre_topc(X0_54)
% 3.81/0.99      | ~ v2_pre_topc(sK3)
% 3.81/0.99      | ~ l1_pre_topc(X0_54)
% 3.81/0.99      | ~ l1_pre_topc(sK3)
% 3.81/0.99      | v2_struct_0(X0_54)
% 3.81/0.99      | v2_struct_0(sK5)
% 3.81/0.99      | v2_struct_0(sK4)
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ v1_funct_1(sK7)
% 3.81/0.99      | ~ v1_funct_1(sK6) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_5672]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6477,plain,
% 3.81/0.99      ( v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 3.81/0.99      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK5,X0_54) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK4,X0_54) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.99      | v2_struct_0(sK5) = iProver_top
% 3.81/0.99      | v2_struct_0(sK4) = iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_6476]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6479,plain,
% 3.81/0.99      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 3.81/0.99      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.99      | v2_struct_0(sK5) = iProver_top
% 3.81/0.99      | v2_struct_0(sK4) = iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v2_struct_0(sK2) = iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_6477]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5671,plain,
% 3.81/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3))
% 3.81/0.99      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.99      | ~ m1_pre_topc(X0_54,X1_54)
% 3.81/0.99      | ~ m1_pre_topc(sK5,X1_54)
% 3.81/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 3.81/0.99      | m1_subset_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))))
% 3.81/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.99      | ~ v2_pre_topc(X1_54)
% 3.81/0.99      | ~ v2_pre_topc(sK3)
% 3.81/0.99      | ~ l1_pre_topc(X1_54)
% 3.81/0.99      | ~ l1_pre_topc(sK3)
% 3.81/0.99      | v2_struct_0(X0_54)
% 3.81/0.99      | v2_struct_0(X1_54)
% 3.81/0.99      | v2_struct_0(sK5)
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ v1_funct_1(X0_52)
% 3.81/0.99      | ~ v1_funct_1(sK7) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_1968]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6313,plain,
% 3.81/0.99      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.81/0.99      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 3.81/0.99      | ~ m1_pre_topc(sK5,X0_54)
% 3.81/0.99      | ~ m1_pre_topc(sK4,X0_54)
% 3.81/0.99      | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))))
% 3.81/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.81/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.81/0.99      | ~ v2_pre_topc(X0_54)
% 3.81/0.99      | ~ v2_pre_topc(sK3)
% 3.81/0.99      | ~ l1_pre_topc(X0_54)
% 3.81/0.99      | ~ l1_pre_topc(sK3)
% 3.81/0.99      | v2_struct_0(X0_54)
% 3.81/0.99      | v2_struct_0(sK5)
% 3.81/0.99      | v2_struct_0(sK4)
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ v1_funct_1(sK7)
% 3.81/0.99      | ~ v1_funct_1(sK6) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_5671]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6314,plain,
% 3.81/0.99      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK5,X0_54) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK4,X0_54) != iProver_top
% 3.81/0.99      | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.81/0.99      | v2_struct_0(sK5) = iProver_top
% 3.81/0.99      | v2_struct_0(sK4) = iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_6313]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6316,plain,
% 3.81/0.99      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.81/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.81/0.99      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.81/0.99      | v2_struct_0(sK5) = iProver_top
% 3.81/0.99      | v2_struct_0(sK4) = iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v2_struct_0(sK2) = iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_6314]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_25,negated_conjecture,
% 3.81/0.99      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 3.81/0.99      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 3.81/0.99      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.81/0.99      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1945,negated_conjecture,
% 3.81/0.99      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 3.81/0.99      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 3.81/0.99      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.81/0.99      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5051,plain,
% 3.81/0.99      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1945]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5816,plain,
% 3.81/0.99      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_5801,c_5051]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5824,plain,
% 3.81/0.99      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_5816,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5825,plain,
% 3.81/0.99      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.81/0.99      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_5824]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5831,plain,
% 3.81/0.99      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.81/0.99      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.81/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.81/0.99      | v1_funct_1(sK7) != iProver_top
% 3.81/0.99      | v1_funct_1(sK6) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_5781,c_5825]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5839,plain,
% 3.81/0.99      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_5831,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_38,negated_conjecture,
% 3.81/0.99      ( v1_borsuk_1(sK5,sK2) ),
% 3.81/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_59,plain,
% 3.81/0.99      ( v1_borsuk_1(sK5,sK2) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_41,negated_conjecture,
% 3.81/0.99      ( v1_borsuk_1(sK4,sK2) ),
% 3.81/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_56,plain,
% 3.81/0.99      ( v1_borsuk_1(sK4,sK2) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(contradiction,plain,
% 3.81/0.99      ( $false ),
% 3.81/0.99      inference(minisat,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_12037,c_8675,c_6479,c_6316,c_6265,c_5839,c_68,c_66,
% 3.81/0.99                 c_65,c_64,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,
% 3.81/0.99                 c_53,c_52,c_51,c_50,c_49]) ).
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.99  
% 3.81/0.99  ------                               Statistics
% 3.81/0.99  
% 3.81/0.99  ------ Selected
% 3.81/0.99  
% 3.81/0.99  total_time:                             0.47
% 3.81/0.99  
%------------------------------------------------------------------------------

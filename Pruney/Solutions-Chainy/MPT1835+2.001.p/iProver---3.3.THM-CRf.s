%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:27 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  226 (6562 expanded)
%              Number of clauses        :  155 (1149 expanded)
%              Number of leaves         :   14 (3091 expanded)
%              Depth                    :   36
%              Number of atoms          : 1950 (162063 expanded)
%              Number of equality atoms :  699 (8120 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal clause size      :   52 (   7 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(flattening,[],[f19])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f36,f35,f34,f33,f32,f31])).

fof(f77,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f37])).

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

fof(f70,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f82,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(definition_folding,[],[f18,f22,f21])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1313,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_3602,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1317,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3606,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

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

cnf(c_1324,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | v1_funct_1(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3572,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_4452,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(sK5,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_53,sK3,X0_53,sK5,X0_52,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3606,c_3572])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_51,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_52,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_53,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_56,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_62,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_63,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5503,plain,
    ( v1_funct_1(k10_tmap_1(X1_53,sK3,X0_53,sK5,X0_52,sK7)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(sK5,X1_53) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4452,c_51,c_52,c_53,c_56,c_62,c_63])).

cnf(c_5504,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(sK5,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k10_tmap_1(X1_53,sK3,X0_53,sK5,X0_52,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5503])).

cnf(c_5520,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_53) != iProver_top
    | m1_pre_topc(sK4,X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_53,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3602,c_5504])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_54,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_58,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_59,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6092,plain,
    ( v1_funct_1(k10_tmap_1(X0_53,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | m1_pre_topc(sK5,X0_53) != iProver_top
    | m1_pre_topc(sK4,X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5520,c_54,c_58,c_59])).

cnf(c_6093,plain,
    ( m1_pre_topc(sK5,X0_53) != iProver_top
    | m1_pre_topc(sK4,X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_53,sK3,sK4,sK5,sK6,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6092])).

cnf(c_37,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1309,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(subtyping,[status(esa)],[c_37])).

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

cnf(c_1325,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | v1_funct_2(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_53,X2_53,X0_53)),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3571,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_53,X2_53,X0_53)),u1_struct_0(X1_53)) = iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_4215,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_53)) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_3571])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_48,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_49,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_50,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_40,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_55,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_38,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_57,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5173,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_53)) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4215,c_48,c_49,c_50,c_54,c_55,c_56,c_57])).

cnf(c_5174,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_53)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5173])).

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

cnf(c_1326,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | m1_subset_1(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_53,X2_53,X0_53)),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3570,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_53,X2_53,X0_53)),u1_struct_0(X1_53)))) = iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_4146,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_3570])).

cnf(c_5192,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4146,c_48,c_49,c_50,c_54,c_55,c_56,c_57])).

cnf(c_5193,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5192])).

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

cnf(c_1319,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X3_53)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3577,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_5209,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(sK2,X2_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_53,X0_53,sK2,X1_53,k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5193,c_3577])).

cnf(c_6659,plain,
    ( v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(sK2,X2_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_53,X0_53,sK2,X1_53,k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5209,c_48,c_49,c_50,c_54,c_55,c_56,c_57,c_4215])).

cnf(c_6660,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X1_53,X2_53) != iProver_top
    | m1_pre_topc(sK2,X2_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_53,X0_53,sK2,X1_53,k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6659])).

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

cnf(c_1320,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | v1_funct_2(k3_tmap_1(X2_53,X1_53,X0_53,X3_53,X0_52),u1_struct_0(X3_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3576,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_53,X1_53,X0_53,X3_53,X0_52),u1_struct_0(X3_53),u1_struct_0(X1_53)) = iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X3_53,X2_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

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

cnf(c_1321,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | m1_subset_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X3_53)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3575,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

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

cnf(c_28,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_556,plain,
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

cnf(c_557,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK6)
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_559,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_36,c_35,c_33])).

cnf(c_560,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_1297,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_560])).

cnf(c_3579,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_3867,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3579,c_1309])).

cnf(c_4935,plain,
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
    inference(superposition,[status(thm)],[c_3575,c_3867])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1323,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X1_53)
    | m1_pre_topc(k1_tsep_1(X1_53,X2_53,X0_53),X1_53)
    | ~ l1_pre_topc(X1_53)
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3573,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_53,X2_53,X0_53),X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_4242,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_3573])).

cnf(c_6576,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4935,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_4242])).

cnf(c_6586,plain,
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
    inference(superposition,[status(thm)],[c_3576,c_6576])).

cnf(c_6951,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6586,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_4242])).

cnf(c_6960,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5193,c_6951])).

cnf(c_61,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_65,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7025,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6960,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65])).

cnf(c_7026,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7025])).

cnf(c_7033,plain,
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
    inference(superposition,[status(thm)],[c_6660,c_7026])).

cnf(c_7259,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7033,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_61,c_62,c_63,c_65,c_4242])).

cnf(c_7266,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
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
    inference(superposition,[status(thm)],[c_5174,c_7259])).

cnf(c_7270,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7266,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65])).

cnf(c_7276,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6093,c_7270])).

cnf(c_7282,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7276,c_48,c_49,c_50,c_55,c_57])).

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

cnf(c_11,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f51])).

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
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_493,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_494,plain,
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
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_498,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | sP1(sK2,sK4,X0,sK5,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_47,c_46,c_45,c_41,c_40,c_39,c_38])).

cnf(c_499,plain,
    ( sP1(sK2,sK4,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_498])).

cnf(c_620,plain,
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
    inference(resolution_lifted,[status(thm)],[c_11,c_499])).

cnf(c_621,plain,
    ( ~ sP0(X0,sK5,X1,sK4,sK2)
    | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_679,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_621])).

cnf(c_680,plain,
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
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_1296,plain,
    ( v5_pre_topc(X0_52,k1_tsep_1(sK2,sK4,sK5),X0_53)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),sK5,X0_53)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),sK4,X0_53)
    | ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_53))
    | ~ v1_funct_2(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_53))
    | ~ v1_funct_2(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_53))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
    | ~ v2_pre_topc(X0_53)
    | ~ l1_pre_topc(X0_53)
    | v2_struct_0(X0_53)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52))
    | ~ v1_funct_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52)) ),
    inference(subtyping,[status(esa)],[c_680])).

cnf(c_3580,plain,
    ( v5_pre_topc(X0_52,k1_tsep_1(sK2,sK4,sK5),X0_53) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),sK5,X0_53) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_4026,plain,
    ( v5_pre_topc(X0_52,sK2,X0_53) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_53,sK2,sK5,X0_52),sK5,X0_53) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_53,sK2,sK4,X0_52),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_53,sK2,sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_53,sK2,sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_53,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_53,sK2,sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_53,sK2,sK5,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_53,sK2,sK4,X0_52)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3580,c_1309])).

cnf(c_7289,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7282,c_4026])).

cnf(c_27,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_536,plain,
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

cnf(c_537,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_539,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_32,c_31,c_29])).

cnf(c_540,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_1298,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_540])).

cnf(c_3578,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_3858,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3578,c_1309])).

cnf(c_4934,plain,
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
    inference(superposition,[status(thm)],[c_3575,c_3858])).

cnf(c_6436,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4934,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_4242])).

cnf(c_6446,plain,
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
    inference(superposition,[status(thm)],[c_3576,c_6436])).

cnf(c_6519,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6446,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_4242])).

cnf(c_6528,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5193,c_6519])).

cnf(c_6532,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6528,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65])).

cnf(c_6533,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6532])).

cnf(c_6681,plain,
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
    inference(superposition,[status(thm)],[c_6660,c_6533])).

cnf(c_7089,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6681,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_61,c_62,c_63,c_65,c_4242])).

cnf(c_7096,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
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
    inference(superposition,[status(thm)],[c_5174,c_7089])).

cnf(c_7110,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7096,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65])).

cnf(c_7116,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6093,c_7110])).

cnf(c_7120,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7116,c_48,c_49,c_50,c_55,c_57])).

cnf(c_7374,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7289,c_7120,c_7282])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_60,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_64,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1318,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3607,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_5208,plain,
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
    inference(superposition,[status(thm)],[c_5193,c_3607])).

cnf(c_5442,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5208,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65])).

cnf(c_5443,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5442])).

cnf(c_5449,plain,
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
    inference(superposition,[status(thm)],[c_5174,c_5443])).

cnf(c_5452,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5449,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65])).

cnf(c_7425,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7374,c_51,c_52,c_53,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_65,c_5452])).

cnf(c_7426,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7425])).

cnf(c_7432,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
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
    inference(superposition,[status(thm)],[c_5193,c_7426])).

cnf(c_7746,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7432,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65])).

cnf(c_7752,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5174,c_7746])).

cnf(c_7790,plain,
    ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7752,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65])).

cnf(c_7795,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6093,c_7790])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7795,c_57,c_55,c_50,c_49,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 09:40:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.62/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.02  
% 3.62/1.02  ------  iProver source info
% 3.62/1.02  
% 3.62/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.02  git: non_committed_changes: false
% 3.62/1.02  git: last_make_outside_of_git: false
% 3.62/1.02  
% 3.62/1.02  ------ 
% 3.62/1.02  ------ Parsing...
% 3.62/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  ------ Proving...
% 3.62/1.02  ------ Problem Properties 
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  clauses                                 39
% 3.62/1.02  conjectures                             20
% 3.62/1.02  EPR                                     14
% 3.62/1.02  Horn                                    22
% 3.62/1.02  unary                                   19
% 3.62/1.02  binary                                  0
% 3.62/1.02  lits                                    211
% 3.62/1.02  lits eq                                 3
% 3.62/1.02  fd_pure                                 0
% 3.62/1.02  fd_pseudo                               0
% 3.62/1.02  fd_cond                                 0
% 3.62/1.02  fd_pseudo_cond                          0
% 3.62/1.02  AC symbols                              0
% 3.62/1.02  
% 3.62/1.02  ------ Input Options Time Limit: Unbounded
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing...
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.62/1.02  Current options:
% 3.62/1.02  ------ 
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 34 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing...
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 38 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing...
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 38 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.62/1.02  
% 3.62/1.02  ------ Proving...
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  % SZS status Theorem for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  fof(f6,conjecture,(
% 3.62/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f7,negated_conjecture,(
% 3.62/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 3.62/1.02    inference(negated_conjecture,[],[f6])).
% 3.62/1.02  
% 3.62/1.02  fof(f19,plain,(
% 3.62/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f7])).
% 3.62/1.02  
% 3.62/1.02  fof(f20,plain,(
% 3.62/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f19])).
% 3.62/1.02  
% 3.62/1.02  fof(f36,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),sK7) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),X4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK7,X3,X1) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f35,plain,(
% 3.62/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),sK6) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK6,X2,X1) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f34,plain,(
% 3.62/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5))) & r4_tsep_1(X0,X2,sK5) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(X5,sK5,X1) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,sK5) = X0 & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f33,plain,(
% 3.62/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5))) & r4_tsep_1(X0,sK4,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(X4,sK4,X1) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,sK4,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f32,plain,(
% 3.62/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),X0,sK3) | ~v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f31,plain,(
% 3.62/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(sK2,X2,X3) = sK2 & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.62/1.02    introduced(choice_axiom,[])).
% 3.62/1.02  
% 3.62/1.02  fof(f37,plain,(
% 3.62/1.02    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & k1_tsep_1(sK2,sK4,sK5) = sK2 & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.62/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f36,f35,f34,f33,f32,f31])).
% 3.62/1.02  
% 3.62/1.02  fof(f77,plain,(
% 3.62/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f81,plain,(
% 3.62/1.02    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f2,axiom,(
% 3.62/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f11,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f2])).
% 3.62/1.02  
% 3.62/1.02  fof(f12,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f11])).
% 3.62/1.02  
% 3.62/1.02  fof(f40,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f12])).
% 3.62/1.02  
% 3.62/1.02  fof(f66,plain,(
% 3.62/1.02    ~v2_struct_0(sK3)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f67,plain,(
% 3.62/1.02    v2_pre_topc(sK3)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f68,plain,(
% 3.62/1.02    l1_pre_topc(sK3)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f71,plain,(
% 3.62/1.02    ~v2_struct_0(sK5)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f78,plain,(
% 3.62/1.02    v1_funct_1(sK7)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f79,plain,(
% 3.62/1.02    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f69,plain,(
% 3.62/1.02    ~v2_struct_0(sK4)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f74,plain,(
% 3.62/1.02    v1_funct_1(sK6)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f75,plain,(
% 3.62/1.02    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f73,plain,(
% 3.62/1.02    k1_tsep_1(sK2,sK4,sK5) = sK2),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f41,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f12])).
% 3.62/1.02  
% 3.62/1.02  fof(f63,plain,(
% 3.62/1.02    ~v2_struct_0(sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f64,plain,(
% 3.62/1.02    v2_pre_topc(sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f65,plain,(
% 3.62/1.02    l1_pre_topc(sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f70,plain,(
% 3.62/1.02    m1_pre_topc(sK4,sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f72,plain,(
% 3.62/1.02    m1_pre_topc(sK5,sK2)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f42,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f12])).
% 3.62/1.02  
% 3.62/1.02  fof(f4,axiom,(
% 3.62/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f15,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f4])).
% 3.62/1.02  
% 3.62/1.02  fof(f16,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f15])).
% 3.62/1.02  
% 3.62/1.02  fof(f45,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f16])).
% 3.62/1.02  
% 3.62/1.02  fof(f46,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f16])).
% 3.62/1.02  
% 3.62/1.02  fof(f47,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f16])).
% 3.62/1.02  
% 3.62/1.02  fof(f1,axiom,(
% 3.62/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f9,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.62/1.02    inference(ennf_transformation,[],[f1])).
% 3.62/1.02  
% 3.62/1.02  fof(f10,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.62/1.02    inference(flattening,[],[f9])).
% 3.62/1.02  
% 3.62/1.02  fof(f24,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.62/1.02    inference(nnf_transformation,[],[f10])).
% 3.62/1.02  
% 3.62/1.02  fof(f38,plain,(
% 3.62/1.02    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f24])).
% 3.62/1.02  
% 3.62/1.02  fof(f82,plain,(
% 3.62/1.02    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f3,axiom,(
% 3.62/1.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f8,plain,(
% 3.62/1.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.62/1.02    inference(pure_predicate_removal,[],[f3])).
% 3.62/1.02  
% 3.62/1.02  fof(f13,plain,(
% 3.62/1.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f8])).
% 3.62/1.02  
% 3.62/1.02  fof(f14,plain,(
% 3.62/1.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f13])).
% 3.62/1.02  
% 3.62/1.02  fof(f44,plain,(
% 3.62/1.02    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f14])).
% 3.62/1.02  
% 3.62/1.02  fof(f21,plain,(
% 3.62/1.02    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 3.62/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.62/1.02  
% 3.62/1.02  fof(f28,plain,(
% 3.62/1.02    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.62/1.02    inference(nnf_transformation,[],[f21])).
% 3.62/1.02  
% 3.62/1.02  fof(f29,plain,(
% 3.62/1.02    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 3.62/1.02    inference(flattening,[],[f28])).
% 3.62/1.02  
% 3.62/1.02  fof(f30,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.62/1.02    inference(rectify,[],[f29])).
% 3.62/1.02  
% 3.62/1.02  fof(f61,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 3.62/1.02    inference(cnf_transformation,[],[f30])).
% 3.62/1.02  
% 3.62/1.02  fof(f22,plain,(
% 3.62/1.02    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 3.62/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.62/1.02  
% 3.62/1.02  fof(f25,plain,(
% 3.62/1.02    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.62/1.02    inference(nnf_transformation,[],[f22])).
% 3.62/1.02  
% 3.62/1.02  fof(f26,plain,(
% 3.62/1.02    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 3.62/1.02    inference(flattening,[],[f25])).
% 3.62/1.02  
% 3.62/1.02  fof(f27,plain,(
% 3.62/1.02    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 3.62/1.02    inference(rectify,[],[f26])).
% 3.62/1.02  
% 3.62/1.02  fof(f51,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f27])).
% 3.62/1.02  
% 3.62/1.02  fof(f5,axiom,(
% 3.62/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 3.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.02  
% 3.62/1.02  fof(f17,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.02    inference(ennf_transformation,[],[f5])).
% 3.62/1.02  
% 3.62/1.02  fof(f18,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(flattening,[],[f17])).
% 3.62/1.02  
% 3.62/1.02  fof(f23,plain,(
% 3.62/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.02    inference(definition_folding,[],[f18,f22,f21])).
% 3.62/1.02  
% 3.62/1.02  fof(f62,plain,(
% 3.62/1.02    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.02    inference(cnf_transformation,[],[f23])).
% 3.62/1.02  
% 3.62/1.02  fof(f84,plain,(
% 3.62/1.02    r4_tsep_1(sK2,sK4,sK5)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f83,plain,(
% 3.62/1.02    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f76,plain,(
% 3.62/1.02    v5_pre_topc(sK6,sK4,sK3)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f80,plain,(
% 3.62/1.02    v5_pre_topc(sK7,sK5,sK3)),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  fof(f85,plain,(
% 3.62/1.02    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 3.62/1.02    inference(cnf_transformation,[],[f37])).
% 3.62/1.02  
% 3.62/1.02  cnf(c_33,negated_conjecture,
% 3.62/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.62/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1313,negated_conjecture,
% 3.62/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_33]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3602,plain,
% 3.62/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_29,negated_conjecture,
% 3.62/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.62/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1317,negated_conjecture,
% 3.62/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_29]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3606,plain,
% 3.62/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.62/1.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.62/1.02      | ~ m1_pre_topc(X1,X5)
% 3.62/1.02      | ~ m1_pre_topc(X4,X5)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.62/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.62/1.02      | ~ v2_pre_topc(X2)
% 3.62/1.02      | ~ v2_pre_topc(X5)
% 3.62/1.02      | ~ l1_pre_topc(X2)
% 3.62/1.02      | ~ l1_pre_topc(X5)
% 3.62/1.02      | v2_struct_0(X5)
% 3.62/1.02      | v2_struct_0(X2)
% 3.62/1.02      | v2_struct_0(X4)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(X3)
% 3.62/1.02      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1324,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.62/1.02      | ~ v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 3.62/1.02      | ~ m1_pre_topc(X2_53,X3_53)
% 3.62/1.02      | ~ m1_pre_topc(X0_53,X3_53)
% 3.62/1.02      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ v2_pre_topc(X1_53)
% 3.62/1.02      | ~ v2_pre_topc(X3_53)
% 3.62/1.02      | ~ l1_pre_topc(X1_53)
% 3.62/1.02      | ~ l1_pre_topc(X3_53)
% 3.62/1.02      | v2_struct_0(X1_53)
% 3.62/1.02      | v2_struct_0(X0_53)
% 3.62/1.02      | v2_struct_0(X2_53)
% 3.62/1.02      | v2_struct_0(X3_53)
% 3.62/1.02      | ~ v1_funct_1(X0_52)
% 3.62/1.02      | ~ v1_funct_1(X1_52)
% 3.62/1.02      | v1_funct_1(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52)) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3572,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X3_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X2_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4452,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,X1_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(sK5) = iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(X1_53,sK3,X0_53,sK5,X0_52,sK7)) = iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_3606,c_3572]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_44,negated_conjecture,
% 3.62/1.02      ( ~ v2_struct_0(sK3) ),
% 3.62/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_51,plain,
% 3.62/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_43,negated_conjecture,
% 3.62/1.02      ( v2_pre_topc(sK3) ),
% 3.62/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_52,plain,
% 3.62/1.02      ( v2_pre_topc(sK3) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_42,negated_conjecture,
% 3.62/1.02      ( l1_pre_topc(sK3) ),
% 3.62/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_53,plain,
% 3.62/1.02      ( l1_pre_topc(sK3) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_39,negated_conjecture,
% 3.62/1.02      ( ~ v2_struct_0(sK5) ),
% 3.62/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_56,plain,
% 3.62/1.02      ( v2_struct_0(sK5) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_32,negated_conjecture,
% 3.62/1.02      ( v1_funct_1(sK7) ),
% 3.62/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_62,plain,
% 3.62/1.02      ( v1_funct_1(sK7) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_31,negated_conjecture,
% 3.62/1.02      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_63,plain,
% 3.62/1.02      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5503,plain,
% 3.62/1.02      ( v1_funct_1(k10_tmap_1(X1_53,sK3,X0_53,sK5,X0_52,sK7)) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,X1_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.62/1.02      | v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_4452,c_51,c_52,c_53,c_56,c_62,c_63]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5504,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,X1_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(X1_53,sK3,X0_53,sK5,X0_52,sK7)) = iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_5503]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5520,plain,
% 3.62/1.02      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,X0_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,X0_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(sK4) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(X0_53,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_3602,c_5504]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_41,negated_conjecture,
% 3.62/1.02      ( ~ v2_struct_0(sK4) ),
% 3.62/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_54,plain,
% 3.62/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_36,negated_conjecture,
% 3.62/1.02      ( v1_funct_1(sK6) ),
% 3.62/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_58,plain,
% 3.62/1.02      ( v1_funct_1(sK6) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_35,negated_conjecture,
% 3.62/1.02      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_59,plain,
% 3.62/1.02      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6092,plain,
% 3.62/1.02      ( v1_funct_1(k10_tmap_1(X0_53,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,X0_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,X0_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_5520,c_54,c_58,c_59]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6093,plain,
% 3.62/1.02      ( m1_pre_topc(sK5,X0_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,X0_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(X0_53,sK3,sK4,sK5,sK6,sK7)) = iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_6092]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_37,negated_conjecture,
% 3.62/1.02      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 3.62/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1309,negated_conjecture,
% 3.62/1.02      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_37]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.62/1.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.62/1.02      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 3.62/1.02      | ~ m1_pre_topc(X1,X5)
% 3.62/1.02      | ~ m1_pre_topc(X4,X5)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.62/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.62/1.02      | ~ v2_pre_topc(X2)
% 3.62/1.02      | ~ v2_pre_topc(X5)
% 3.62/1.02      | ~ l1_pre_topc(X2)
% 3.62/1.02      | ~ l1_pre_topc(X5)
% 3.62/1.02      | v2_struct_0(X5)
% 3.62/1.02      | v2_struct_0(X2)
% 3.62/1.02      | v2_struct_0(X4)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(X3) ),
% 3.62/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1325,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.62/1.02      | ~ v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 3.62/1.02      | v1_funct_2(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_53,X2_53,X0_53)),u1_struct_0(X1_53))
% 3.62/1.02      | ~ m1_pre_topc(X2_53,X3_53)
% 3.62/1.02      | ~ m1_pre_topc(X0_53,X3_53)
% 3.62/1.02      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ v2_pre_topc(X1_53)
% 3.62/1.02      | ~ v2_pre_topc(X3_53)
% 3.62/1.02      | ~ l1_pre_topc(X1_53)
% 3.62/1.02      | ~ l1_pre_topc(X3_53)
% 3.62/1.02      | v2_struct_0(X1_53)
% 3.62/1.02      | v2_struct_0(X0_53)
% 3.62/1.02      | v2_struct_0(X2_53)
% 3.62/1.02      | v2_struct_0(X3_53)
% 3.62/1.02      | ~ v1_funct_1(X0_52)
% 3.62/1.02      | ~ v1_funct_1(X1_52) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3571,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_53,X2_53,X0_53)),u1_struct_0(X1_53)) = iProver_top
% 3.62/1.02      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X3_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X2_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1325]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4215,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_53)) = iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(sK5) = iProver_top
% 3.62/1.02      | v2_struct_0(sK4) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1309,c_3571]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_47,negated_conjecture,
% 3.62/1.02      ( ~ v2_struct_0(sK2) ),
% 3.62/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_48,plain,
% 3.62/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_46,negated_conjecture,
% 3.62/1.02      ( v2_pre_topc(sK2) ),
% 3.62/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_49,plain,
% 3.62/1.02      ( v2_pre_topc(sK2) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_45,negated_conjecture,
% 3.62/1.02      ( l1_pre_topc(sK2) ),
% 3.62/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_50,plain,
% 3.62/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_40,negated_conjecture,
% 3.62/1.02      ( m1_pre_topc(sK4,sK2) ),
% 3.62/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_55,plain,
% 3.62/1.02      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_38,negated_conjecture,
% 3.62/1.02      ( m1_pre_topc(sK5,sK2) ),
% 3.62/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_57,plain,
% 3.62/1.02      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5173,plain,
% 3.62/1.02      ( v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_53)) = iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_4215,c_48,c_49,c_50,c_54,c_55,c_56,c_57]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5174,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_53)) = iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_5173]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_2,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.62/1.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.62/1.02      | ~ m1_pre_topc(X1,X5)
% 3.62/1.02      | ~ m1_pre_topc(X4,X5)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.62/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.62/1.02      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 3.62/1.02      | ~ v2_pre_topc(X2)
% 3.62/1.02      | ~ v2_pre_topc(X5)
% 3.62/1.02      | ~ l1_pre_topc(X2)
% 3.62/1.02      | ~ l1_pre_topc(X5)
% 3.62/1.02      | v2_struct_0(X5)
% 3.62/1.02      | v2_struct_0(X2)
% 3.62/1.02      | v2_struct_0(X4)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(X3) ),
% 3.62/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1326,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.62/1.02      | ~ v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 3.62/1.02      | ~ m1_pre_topc(X2_53,X3_53)
% 3.62/1.02      | ~ m1_pre_topc(X0_53,X3_53)
% 3.62/1.02      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.62/1.02      | m1_subset_1(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_53,X2_53,X0_53)),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ v2_pre_topc(X1_53)
% 3.62/1.02      | ~ v2_pre_topc(X3_53)
% 3.62/1.02      | ~ l1_pre_topc(X1_53)
% 3.62/1.02      | ~ l1_pre_topc(X3_53)
% 3.62/1.02      | v2_struct_0(X1_53)
% 3.62/1.02      | v2_struct_0(X0_53)
% 3.62/1.02      | v2_struct_0(X2_53)
% 3.62/1.02      | v2_struct_0(X3_53)
% 3.62/1.02      | ~ v1_funct_1(X0_52)
% 3.62/1.02      | ~ v1_funct_1(X1_52) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3570,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(X3_53,X1_53,X2_53,X0_53,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_53,X2_53,X0_53)),u1_struct_0(X1_53)))) = iProver_top
% 3.62/1.02      | v2_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X3_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X2_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4146,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) = iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(sK5) = iProver_top
% 3.62/1.02      | v2_struct_0(sK4) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1309,c_3570]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5192,plain,
% 3.62/1.02      ( v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) = iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_4146,c_48,c_49,c_50,c_54,c_55,c_56,c_57]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5193,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) = iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_5192]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_9,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.62/1.02      | ~ m1_pre_topc(X3,X4)
% 3.62/1.02      | ~ m1_pre_topc(X1,X4)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.62/1.02      | ~ v2_pre_topc(X2)
% 3.62/1.02      | ~ v2_pre_topc(X4)
% 3.62/1.02      | ~ l1_pre_topc(X2)
% 3.62/1.02      | ~ l1_pre_topc(X4)
% 3.62/1.02      | v2_struct_0(X4)
% 3.62/1.02      | v2_struct_0(X2)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1319,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.62/1.02      | ~ m1_pre_topc(X2_53,X3_53)
% 3.62/1.02      | ~ m1_pre_topc(X0_53,X3_53)
% 3.62/1.02      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ v2_pre_topc(X1_53)
% 3.62/1.02      | ~ v2_pre_topc(X3_53)
% 3.62/1.02      | ~ l1_pre_topc(X1_53)
% 3.62/1.02      | ~ l1_pre_topc(X3_53)
% 3.62/1.02      | v2_struct_0(X1_53)
% 3.62/1.02      | v2_struct_0(X3_53)
% 3.62/1.02      | ~ v1_funct_1(X0_52)
% 3.62/1.02      | v1_funct_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52)) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3577,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X3_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52)) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5209,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,X2_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X2_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X2_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X2_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(X2_53,X0_53,sK2,X1_53,k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5193,c_3577]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6659,plain,
% 3.62/1.02      ( v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,X2_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X2_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X2_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X2_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(X2_53,X0_53,sK2,X1_53,k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_5209,c_48,c_49,c_50,c_54,c_55,c_56,c_57,c_4215]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6660,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X1_53,X2_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,X2_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X2_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X2_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X2_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(X1_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(X2_53,X0_53,sK2,X1_53,k10_tmap_1(sK2,X0_53,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_6659]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_8,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.62/1.02      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.62/1.02      | ~ m1_pre_topc(X4,X3)
% 3.62/1.02      | ~ m1_pre_topc(X1,X3)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.62/1.02      | ~ v2_pre_topc(X2)
% 3.62/1.02      | ~ v2_pre_topc(X3)
% 3.62/1.02      | ~ l1_pre_topc(X2)
% 3.62/1.02      | ~ l1_pre_topc(X3)
% 3.62/1.02      | v2_struct_0(X3)
% 3.62/1.02      | v2_struct_0(X2)
% 3.62/1.02      | ~ v1_funct_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1320,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.62/1.02      | v1_funct_2(k3_tmap_1(X2_53,X1_53,X0_53,X3_53,X0_52),u1_struct_0(X3_53),u1_struct_0(X1_53))
% 3.62/1.02      | ~ m1_pre_topc(X3_53,X2_53)
% 3.62/1.02      | ~ m1_pre_topc(X0_53,X2_53)
% 3.62/1.02      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ v2_pre_topc(X1_53)
% 3.62/1.02      | ~ v2_pre_topc(X2_53)
% 3.62/1.02      | ~ l1_pre_topc(X1_53)
% 3.62/1.02      | ~ l1_pre_topc(X2_53)
% 3.62/1.02      | v2_struct_0(X1_53)
% 3.62/1.02      | v2_struct_0(X2_53)
% 3.62/1.02      | ~ v1_funct_1(X0_52) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3576,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(X2_53,X1_53,X0_53,X3_53,X0_52),u1_struct_0(X3_53),u1_struct_0(X1_53)) = iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(X3_53,X2_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X2_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X2_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X2_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.62/1.02      | ~ m1_pre_topc(X3,X4)
% 3.62/1.02      | ~ m1_pre_topc(X1,X4)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.62/1.02      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.62/1.02      | ~ v2_pre_topc(X2)
% 3.62/1.02      | ~ v2_pre_topc(X4)
% 3.62/1.02      | ~ l1_pre_topc(X2)
% 3.62/1.02      | ~ l1_pre_topc(X4)
% 3.62/1.02      | v2_struct_0(X4)
% 3.62/1.02      | v2_struct_0(X2)
% 3.62/1.02      | ~ v1_funct_1(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1321,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.62/1.02      | ~ m1_pre_topc(X2_53,X3_53)
% 3.62/1.02      | ~ m1_pre_topc(X0_53,X3_53)
% 3.62/1.02      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.62/1.02      | m1_subset_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.62/1.02      | ~ v2_pre_topc(X1_53)
% 3.62/1.02      | ~ v2_pre_topc(X3_53)
% 3.62/1.02      | ~ l1_pre_topc(X1_53)
% 3.62/1.02      | ~ l1_pre_topc(X3_53)
% 3.62/1.02      | v2_struct_0(X1_53)
% 3.62/1.02      | v2_struct_0(X3_53)
% 3.62/1.02      | ~ v1_funct_1(X0_52) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3575,plain,
% 3.62/1.02      ( v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.62/1.02      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
% 3.62/1.02      | v2_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | v2_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X3_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X3_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1,plain,
% 3.62/1.02      ( ~ r2_funct_2(X0,X1,X2,X3)
% 3.62/1.02      | ~ v1_funct_2(X3,X0,X1)
% 3.62/1.02      | ~ v1_funct_2(X2,X0,X1)
% 3.62/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.62/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.62/1.02      | ~ v1_funct_1(X3)
% 3.62/1.02      | ~ v1_funct_1(X2)
% 3.62/1.02      | X2 = X3 ),
% 3.62/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_28,negated_conjecture,
% 3.62/1.02      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
% 3.62/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_556,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/1.02      | ~ v1_funct_2(X3,X1,X2)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(X3)
% 3.62/1.02      | X3 = X0
% 3.62/1.02      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 3.62/1.02      | u1_struct_0(sK4) != X1
% 3.62/1.02      | u1_struct_0(sK3) != X2
% 3.62/1.02      | sK6 != X3 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_28]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_557,plain,
% 3.62/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.62/1.02      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.62/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.62/1.02      | ~ v1_funct_1(sK6)
% 3.62/1.02      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_556]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_559,plain,
% 3.62/1.02      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.62/1.02      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_557,c_36,c_35,c_33]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_560,plain,
% 3.62/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.62/1.02      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_559]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1297,plain,
% 3.62/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.62/1.02      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_560]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3579,plain,
% 3.62/1.02      ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1297]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3867,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_3579,c_1309]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4935,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_3575,c_3867]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5,plain,
% 3.62/1.02      ( ~ m1_pre_topc(X0,X1)
% 3.62/1.02      | ~ m1_pre_topc(X2,X1)
% 3.62/1.02      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | v2_struct_0(X2)
% 3.62/1.02      | v2_struct_0(X0) ),
% 3.62/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1323,plain,
% 3.62/1.02      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.62/1.02      | ~ m1_pre_topc(X2_53,X1_53)
% 3.62/1.02      | m1_pre_topc(k1_tsep_1(X1_53,X2_53,X0_53),X1_53)
% 3.62/1.02      | ~ l1_pre_topc(X1_53)
% 3.62/1.02      | v2_struct_0(X1_53)
% 3.62/1.02      | v2_struct_0(X0_53)
% 3.62/1.02      | v2_struct_0(X2_53) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3573,plain,
% 3.62/1.02      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(X2_53,X1_53) != iProver_top
% 3.62/1.02      | m1_pre_topc(k1_tsep_1(X1_53,X2_53,X0_53),X1_53) = iProver_top
% 3.62/1.02      | l1_pre_topc(X1_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X1_53) = iProver_top
% 3.62/1.02      | v2_struct_0(X2_53) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4242,plain,
% 3.62/1.02      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,sK2) = iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK5) = iProver_top
% 3.62/1.02      | v2_struct_0(sK4) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_1309,c_3573]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6576,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_4935,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,
% 3.62/1.02                 c_57,c_4242]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6586,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_3576,c_6576]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6951,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_6586,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,
% 3.62/1.02                 c_57,c_4242]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6960,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5193,c_6951]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_61,plain,
% 3.62/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_65,plain,
% 3.62/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7025,plain,
% 3.62/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_6960,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7026,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_7025]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7033,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_6660,c_7026]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7259,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_7033,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,
% 3.62/1.02                 c_57,c_58,c_59,c_61,c_62,c_63,c_65,c_4242]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7266,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5174,c_7259]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7270,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_7266,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7276,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 3.62/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_6093,c_7270]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7282,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_7276,c_48,c_49,c_50,c_55,c_57]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_15,plain,
% 3.62/1.02      ( sP0(X0,X1,X2,X3,X4)
% 3.62/1.02      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 3.62/1.02      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_11,plain,
% 3.62/1.02      ( ~ sP1(X0,X1,X2,X3,X4)
% 3.62/1.02      | ~ sP0(X4,X3,X2,X1,X0)
% 3.62/1.02      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 3.62/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_24,plain,
% 3.62/1.02      ( sP1(X0,X1,X2,X3,X4)
% 3.62/1.02      | ~ r4_tsep_1(X0,X1,X3)
% 3.62/1.02      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.62/1.02      | ~ m1_pre_topc(X3,X0)
% 3.62/1.02      | ~ m1_pre_topc(X1,X0)
% 3.62/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.62/1.02      | ~ v2_pre_topc(X4)
% 3.62/1.02      | ~ v2_pre_topc(X0)
% 3.62/1.02      | ~ l1_pre_topc(X4)
% 3.62/1.02      | ~ l1_pre_topc(X0)
% 3.62/1.02      | v2_struct_0(X0)
% 3.62/1.02      | v2_struct_0(X4)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | v2_struct_0(X3)
% 3.62/1.02      | ~ v1_funct_1(X2) ),
% 3.62/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_26,negated_conjecture,
% 3.62/1.02      ( r4_tsep_1(sK2,sK4,sK5) ),
% 3.62/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_493,plain,
% 3.62/1.02      ( sP1(X0,X1,X2,X3,X4)
% 3.62/1.02      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 3.62/1.02      | ~ m1_pre_topc(X3,X0)
% 3.62/1.02      | ~ m1_pre_topc(X1,X0)
% 3.62/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 3.62/1.02      | ~ v2_pre_topc(X0)
% 3.62/1.02      | ~ v2_pre_topc(X4)
% 3.62/1.02      | ~ l1_pre_topc(X0)
% 3.62/1.02      | ~ l1_pre_topc(X4)
% 3.62/1.02      | v2_struct_0(X0)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | v2_struct_0(X3)
% 3.62/1.02      | v2_struct_0(X4)
% 3.62/1.02      | ~ v1_funct_1(X2)
% 3.62/1.02      | sK5 != X3
% 3.62/1.02      | sK4 != X1
% 3.62/1.02      | sK2 != X0 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_494,plain,
% 3.62/1.02      ( sP1(sK2,sK4,X0,sK5,X1)
% 3.62/1.02      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 3.62/1.02      | ~ m1_pre_topc(sK5,sK2)
% 3.62/1.02      | ~ m1_pre_topc(sK4,sK2)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 3.62/1.02      | ~ v2_pre_topc(X1)
% 3.62/1.02      | ~ v2_pre_topc(sK2)
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | ~ l1_pre_topc(sK2)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | v2_struct_0(sK5)
% 3.62/1.02      | v2_struct_0(sK4)
% 3.62/1.02      | v2_struct_0(sK2)
% 3.62/1.02      | ~ v1_funct_1(X0) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_493]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_498,plain,
% 3.62/1.02      ( v2_struct_0(X1)
% 3.62/1.02      | ~ v2_pre_topc(X1)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 3.62/1.02      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 3.62/1.02      | sP1(sK2,sK4,X0,sK5,X1)
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | ~ v1_funct_1(X0) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_494,c_47,c_46,c_45,c_41,c_40,c_39,c_38]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_499,plain,
% 3.62/1.02      ( sP1(sK2,sK4,X0,sK5,X1)
% 3.62/1.02      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 3.62/1.02      | ~ v2_pre_topc(X1)
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | ~ v1_funct_1(X0) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_498]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_620,plain,
% 3.62/1.02      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.62/1.02      | v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
% 3.62/1.02      | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
% 3.62/1.02      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
% 3.62/1.02      | ~ v2_pre_topc(X6)
% 3.62/1.02      | ~ l1_pre_topc(X6)
% 3.62/1.02      | v2_struct_0(X6)
% 3.62/1.02      | ~ v1_funct_1(X5)
% 3.62/1.02      | X5 != X2
% 3.62/1.02      | X6 != X0
% 3.62/1.02      | sK5 != X1
% 3.62/1.02      | sK4 != X3
% 3.62/1.02      | sK2 != X4 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_499]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_621,plain,
% 3.62/1.02      ( ~ sP0(X0,sK5,X1,sK4,sK2)
% 3.62/1.02      | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
% 3.62/1.02      | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
% 3.62/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
% 3.62/1.02      | ~ v2_pre_topc(X0)
% 3.62/1.02      | ~ l1_pre_topc(X0)
% 3.62/1.02      | v2_struct_0(X0)
% 3.62/1.02      | ~ v1_funct_1(X1) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_620]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_679,plain,
% 3.62/1.02      ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 3.62/1.02      | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),X5,X3)
% 3.62/1.02      | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),X4,X3)
% 3.62/1.02      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),u1_struct_0(X5),u1_struct_0(X3))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
% 3.62/1.02      | ~ v2_pre_topc(X1)
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
% 3.62/1.02      | X0 != X6
% 3.62/1.02      | X1 != X3
% 3.62/1.02      | sK5 != X5
% 3.62/1.02      | sK4 != X4
% 3.62/1.02      | sK2 != X2 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_621]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_680,plain,
% 3.62/1.02      ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 3.62/1.02      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),sK5,X1)
% 3.62/1.02      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),sK4,X1)
% 3.62/1.02      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),u1_struct_0(sK5),u1_struct_0(X1))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 3.62/1.02      | ~ v2_pre_topc(X1)
% 3.62/1.02      | ~ l1_pre_topc(X1)
% 3.62/1.02      | v2_struct_0(X1)
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_679]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1296,plain,
% 3.62/1.02      ( v5_pre_topc(X0_52,k1_tsep_1(sK2,sK4,sK5),X0_53)
% 3.62/1.02      | ~ v5_pre_topc(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),sK5,X0_53)
% 3.62/1.02      | ~ v5_pre_topc(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),sK4,X0_53)
% 3.62/1.02      | ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_53))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_53))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_53))
% 3.62/1.02      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_53))))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53))))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
% 3.62/1.02      | ~ v2_pre_topc(X0_53)
% 3.62/1.02      | ~ l1_pre_topc(X0_53)
% 3.62/1.02      | v2_struct_0(X0_53)
% 3.62/1.02      | ~ v1_funct_1(X0_52)
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52)) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_680]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3580,plain,
% 3.62/1.02      ( v5_pre_topc(X0_52,k1_tsep_1(sK2,sK4,sK5),X0_53) = iProver_top
% 3.62/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),sK5,X0_53) != iProver_top
% 3.62/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),sK4,X0_53) != iProver_top
% 3.62/1.02      | v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_53,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4026,plain,
% 3.62/1.02      ( v5_pre_topc(X0_52,sK2,X0_53) = iProver_top
% 3.62/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_53,sK2,sK5,X0_52),sK5,X0_53) != iProver_top
% 3.62/1.02      | v5_pre_topc(k3_tmap_1(sK2,X0_53,sK2,sK4,X0_52),sK4,X0_53) != iProver_top
% 3.62/1.02      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_53,sK2,sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,X0_53,sK2,sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_53)) != iProver_top
% 3.62/1.02      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_53,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,X0_53,sK2,sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | l1_pre_topc(X0_53) != iProver_top
% 3.62/1.02      | v2_struct_0(X0_53) = iProver_top
% 3.62/1.02      | v1_funct_1(X0_52) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_53,sK2,sK5,X0_52)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,X0_53,sK2,sK4,X0_52)) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_3580,c_1309]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7289,plain,
% 3.62/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top
% 3.62/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
% 3.62/1.02      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_7282,c_4026]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_27,negated_conjecture,
% 3.62/1.02      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
% 3.62/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_536,plain,
% 3.62/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/1.02      | ~ v1_funct_2(X3,X1,X2)
% 3.62/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.02      | ~ v1_funct_1(X0)
% 3.62/1.02      | ~ v1_funct_1(X3)
% 3.62/1.02      | X3 = X0
% 3.62/1.02      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 3.62/1.02      | u1_struct_0(sK5) != X1
% 3.62/1.02      | u1_struct_0(sK3) != X2
% 3.62/1.02      | sK7 != X3 ),
% 3.62/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_27]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_537,plain,
% 3.62/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.62/1.02      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.62/1.02      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.62/1.02      | ~ v1_funct_1(sK7)
% 3.62/1.02      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(unflattening,[status(thm)],[c_536]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_539,plain,
% 3.62/1.02      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.62/1.02      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.62/1.02      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_537,c_32,c_31,c_29]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_540,plain,
% 3.62/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.62/1.02      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_539]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1298,plain,
% 3.62/1.02      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 3.62/1.02      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 3.62/1.02      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_540]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3578,plain,
% 3.62/1.02      ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1298]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3858,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_3578,c_1309]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_4934,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_3575,c_3858]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6436,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_4934,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,
% 3.62/1.02                 c_57,c_4242]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6446,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_3576,c_6436]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6519,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_6446,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,
% 3.62/1.02                 c_57,c_4242]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6528,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5193,c_6519]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6532,plain,
% 3.62/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_6528,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6533,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_6532]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_6681,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_6660,c_6533]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7089,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_6681,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,
% 3.62/1.02                 c_57,c_58,c_59,c_61,c_62,c_63,c_65,c_4242]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7096,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5174,c_7089]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7110,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_7096,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7116,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 3.62/1.02      | m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_6093,c_7110]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7120,plain,
% 3.62/1.02      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_7116,c_48,c_49,c_50,c_55,c_57]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7374,plain,
% 3.62/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top
% 3.62/1.02      | v5_pre_topc(sK7,sK5,sK3) != iProver_top
% 3.62/1.02      | v5_pre_topc(sK6,sK4,sK3) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(light_normalisation,[status(thm)],[c_7289,c_7120,c_7282]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_34,negated_conjecture,
% 3.62/1.02      ( v5_pre_topc(sK6,sK4,sK3) ),
% 3.62/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_60,plain,
% 3.62/1.02      ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_30,negated_conjecture,
% 3.62/1.02      ( v5_pre_topc(sK7,sK5,sK3) ),
% 3.62/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_64,plain,
% 3.62/1.02      ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_25,negated_conjecture,
% 3.62/1.02      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 3.62/1.02      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.62/1.02      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_1318,negated_conjecture,
% 3.62/1.02      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 3.62/1.02      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 3.62/1.02      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.62/1.02      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 3.62/1.02      inference(subtyping,[status(esa)],[c_25]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_3607,plain,
% 3.62/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5208,plain,
% 3.62/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5193,c_3607]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5442,plain,
% 3.62/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_5208,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5443,plain,
% 3.62/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_5442]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5449,plain,
% 3.62/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5174,c_5443]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_5452,plain,
% 3.62/1.02      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_5449,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7425,plain,
% 3.62/1.02      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_7374,c_51,c_52,c_53,c_58,c_59,c_60,c_61,c_62,c_63,
% 3.62/1.02                 c_64,c_65,c_5452]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7426,plain,
% 3.62/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(renaming,[status(thm)],[c_7425]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7432,plain,
% 3.62/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5193,c_7426]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7746,plain,
% 3.62/1.02      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_7432,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7752,plain,
% 3.62/1.02      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.62/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK3) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK3) != iProver_top
% 3.62/1.02      | v2_struct_0(sK3) = iProver_top
% 3.62/1.02      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 3.62/1.02      | v1_funct_1(sK7) != iProver_top
% 3.62/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_5174,c_7746]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7790,plain,
% 3.62/1.02      ( v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 3.62/1.02      inference(global_propositional_subsumption,
% 3.62/1.02                [status(thm)],
% 3.62/1.02                [c_7752,c_51,c_52,c_53,c_58,c_59,c_61,c_62,c_63,c_65]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(c_7795,plain,
% 3.62/1.02      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.62/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.62/1.02      | v2_pre_topc(sK2) != iProver_top
% 3.62/1.02      | l1_pre_topc(sK2) != iProver_top
% 3.62/1.02      | v2_struct_0(sK2) = iProver_top ),
% 3.62/1.02      inference(superposition,[status(thm)],[c_6093,c_7790]) ).
% 3.62/1.02  
% 3.62/1.02  cnf(contradiction,plain,
% 3.62/1.02      ( $false ),
% 3.62/1.02      inference(minisat,[status(thm)],[c_7795,c_57,c_55,c_50,c_49,c_48]) ).
% 3.62/1.02  
% 3.62/1.02  
% 3.62/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.02  
% 3.62/1.02  ------                               Statistics
% 3.62/1.02  
% 3.62/1.02  ------ Selected
% 3.62/1.02  
% 3.62/1.02  total_time:                             0.458
% 3.62/1.02  
%------------------------------------------------------------------------------

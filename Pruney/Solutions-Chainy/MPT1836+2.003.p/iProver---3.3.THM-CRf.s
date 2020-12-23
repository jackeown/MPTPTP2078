%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:28 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  243 (7199 expanded)
%              Number of clauses        :  168 (1327 expanded)
%              Number of leaves         :   15 (3346 expanded)
%              Depth                    :   32
%              Number of atoms          : 2044 (180980 expanded)
%              Number of equality atoms :  738 (11013 expanded)
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
    inference(negated_conjecture,[],[f7])).

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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f21,f37,f36,f35,f34,f33,f32])).

fof(f84,plain,(
    k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f38])).

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

fof(f42,plain,(
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

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(flattening,[],[f13])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f14])).

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

fof(f25,plain,(
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

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
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

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f23,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(nnf_transformation,[],[f23])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f24,plain,(
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
    inference(definition_folding,[],[f16,f23,f22])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_28,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1996,negated_conjecture,
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
    inference(cnf_transformation,[],[f42])).

cnf(c_2017,plain,
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

cnf(c_5037,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_5657,plain,
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
    inference(superposition,[status(thm)],[c_1996,c_5037])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_50,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_51,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_55,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_40,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_57,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_58,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_60,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5753,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5657,c_49,c_50,c_51,c_55,c_57,c_58,c_60])).

cnf(c_5754,plain,
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
    inference(renaming,[status(thm)],[c_5753])).

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
    inference(cnf_transformation,[],[f43])).

cnf(c_2018,plain,
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

cnf(c_5036,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2018])).

cnf(c_5546,plain,
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
    inference(superposition,[status(thm)],[c_1996,c_5036])).

cnf(c_5775,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5546,c_49,c_50,c_51,c_55,c_57,c_58,c_60])).

cnf(c_5776,plain,
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
    inference(renaming,[status(thm)],[c_5775])).

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
    inference(cnf_transformation,[],[f44])).

cnf(c_2013,plain,
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
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_5041,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_7866,plain,
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
    inference(superposition,[status(thm)],[c_5776,c_5041])).

cnf(c_11780,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_7866,c_49,c_50,c_51,c_55,c_57,c_58,c_60,c_5657])).

cnf(c_11781,plain,
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
    inference(renaming,[status(thm)],[c_11780])).

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
    inference(cnf_transformation,[],[f45])).

cnf(c_2014,plain,
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
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_5040,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2014])).

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
    inference(cnf_transformation,[],[f46])).

cnf(c_2015,plain,
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
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_5039,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_26,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_560,plain,
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

cnf(c_561,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_563,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_32,c_31,c_29])).

cnf(c_564,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_563])).

cnf(c_1974,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_564])).

cnf(c_5058,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_5244,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5058,c_1996])).

cnf(c_6679,plain,
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
    inference(superposition,[status(thm)],[c_5039,c_5244])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_52,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_53,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_54,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_61,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_62,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_23,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_75,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_77,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1991,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_5075,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1991])).

cnf(c_1995,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_5079,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1995])).

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
    inference(cnf_transformation,[],[f41])).

cnf(c_2016,plain,
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

cnf(c_5038,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_5870,plain,
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
    inference(superposition,[status(thm)],[c_5079,c_5038])).

cnf(c_65,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_66,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6138,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5870,c_52,c_53,c_54,c_58,c_65,c_66])).

cnf(c_6139,plain,
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
    inference(renaming,[status(thm)],[c_6138])).

cnf(c_6155,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5075,c_6139])).

cnf(c_6282,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6155])).

cnf(c_6960,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6679,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,c_61,c_62,c_77,c_6282])).

cnf(c_6961,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6960])).

cnf(c_7128,plain,
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
    inference(superposition,[status(thm)],[c_5040,c_6961])).

cnf(c_12199,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7128,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,c_61,c_62,c_77,c_6282])).

cnf(c_12200,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12199])).

cnf(c_12207,plain,
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
    inference(superposition,[status(thm)],[c_5776,c_12200])).

cnf(c_64,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_68,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12240,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12207,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_12241,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12240])).

cnf(c_12248,plain,
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
    inference(superposition,[status(thm)],[c_11781,c_12241])).

cnf(c_12458,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12248,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,c_61,c_62,c_64,c_65,c_66,c_68,c_77,c_6282])).

cnf(c_12459,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12458])).

cnf(c_12464,plain,
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
    inference(superposition,[status(thm)],[c_5754,c_12459])).

cnf(c_12469,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12464,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2007,plain,
    ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55)
    | ~ v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),X1_55,X0_55)
    | ~ v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),X2_55,X0_55)
    | ~ v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X0_55))
    | ~ v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55))
    | ~ m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X0_55))))
    | ~ v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53))
    | ~ v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_5047,plain,
    ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),X1_55,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),X2_55,X0_55) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2007])).

cnf(c_10244,plain,
    ( sP0(X0_55,sK5,X0_53,sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_55) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1996,c_5047])).

cnf(c_10254,plain,
    ( sP0(X0_55,sK5,X0_53,sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),sK5,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),sK4,X0_55) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10244,c_1996])).

cnf(c_12474,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12469,c_10254])).

cnf(c_27,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_580,plain,
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

cnf(c_581,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK6)
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_583,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_581,c_36,c_35,c_33])).

cnf(c_584,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_583])).

cnf(c_1973,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_584])).

cnf(c_5059,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1973])).

cnf(c_5253,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5059,c_1996])).

cnf(c_6680,plain,
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
    inference(superposition,[status(thm)],[c_5039,c_5253])).

cnf(c_6993,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6680,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,c_61,c_62,c_77,c_6282])).

cnf(c_6994,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6993])).

cnf(c_7129,plain,
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
    inference(superposition,[status(thm)],[c_5040,c_6994])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2000,plain,
    ( ~ sP0(X0_55,X1_55,X0_53,X2_55,X3_55)
    | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_5054,plain,
    ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_7232,plain,
    ( sP0(X0_55,sK5,X0_53,sK4,sK2) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1996,c_5054])).

cnf(c_7284,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7232,c_6994])).

cnf(c_7558,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7284,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,c_61,c_62,c_77,c_6282,c_7129])).

cnf(c_7566,plain,
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
    inference(superposition,[status(thm)],[c_5776,c_7558])).

cnf(c_7673,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7566,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_7674,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7673])).

cnf(c_11802,plain,
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
    inference(superposition,[status(thm)],[c_11781,c_7674])).

cnf(c_12306,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7129,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,c_61,c_62,c_64,c_65,c_66,c_68,c_77,c_6282,c_11802])).

cnf(c_12307,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12306])).

cnf(c_12312,plain,
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
    inference(superposition,[status(thm)],[c_5754,c_12307])).

cnf(c_12331,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12312,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_12568,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12474,c_12331,c_12469])).

cnf(c_34,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_63,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_67,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12729,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12568,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_68])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2011,plain,
    ( ~ sP1(X0_55,X1_55,X0_53,X2_55,X3_55)
    | ~ sP0(X3_55,X2_55,X0_53,X1_55,X0_55)
    | v5_pre_topc(X0_53,k1_tsep_1(X0_55,X1_55,X2_55),X3_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_5043,plain,
    ( sP1(X0_55,X1_55,X0_53,X2_55,X3_55) != iProver_top
    | sP0(X3_55,X2_55,X0_53,X1_55,X0_55) != iProver_top
    | v5_pre_topc(X0_53,k1_tsep_1(X0_55,X1_55,X2_55),X3_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2011])).

cnf(c_8402,plain,
    ( sP1(sK2,sK4,X0_53,sK5,X0_55) != iProver_top
    | sP0(X0_55,sK5,X0_53,sK4,sK2) != iProver_top
    | v5_pre_topc(X0_53,sK2,X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_1996,c_5043])).

cnf(c_12735,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_12729,c_8402])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_24,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ v1_borsuk_1(X2,X0)
    | ~ v1_borsuk_1(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_503,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_borsuk_1(X5,X6)
    | ~ v1_borsuk_1(X7,X6)
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
    inference(resolution_lifted,[status(thm)],[c_22,c_24])).

cnf(c_504,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ v1_borsuk_1(X3,X0)
    | ~ v1_borsuk_1(X1,X0)
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
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1975,plain,
    ( sP1(X0_55,X1_55,X0_53,X2_55,X3_55)
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55))
    | ~ v1_borsuk_1(X1_55,X0_55)
    | ~ v1_borsuk_1(X2_55,X0_55)
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
    inference(subtyping,[status(esa)],[c_504])).

cnf(c_8589,plain,
    ( sP1(X0_55,sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
    | ~ v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_borsuk_1(sK5,X0_55)
    | ~ v1_borsuk_1(sK4,X0_55)
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
    inference(instantiation,[status(thm)],[c_1975])).

cnf(c_8595,plain,
    ( sP1(X0_55,sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
    | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_borsuk_1(sK5,X0_55) != iProver_top
    | v1_borsuk_1(sK4,X0_55) != iProver_top
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
    inference(predicate_to_equality,[status(thm)],[c_8589])).

cnf(c_8597,plain,
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
    inference(instantiation,[status(thm)],[c_8595])).

cnf(c_5662,plain,
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
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_6340,plain,
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
    inference(instantiation,[status(thm)],[c_5662])).

cnf(c_6341,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_6340])).

cnf(c_6343,plain,
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
    inference(instantiation,[status(thm)],[c_6341])).

cnf(c_5661,plain,
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
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_6312,plain,
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
    inference(instantiation,[status(thm)],[c_5661])).

cnf(c_6313,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_6312])).

cnf(c_6315,plain,
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
    inference(instantiation,[status(thm)],[c_6313])).

cnf(c_25,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1997,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_5080,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1997])).

cnf(c_5791,plain,
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
    inference(superposition,[status(thm)],[c_5776,c_5080])).

cnf(c_5799,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5791,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_5800,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5799])).

cnf(c_5806,plain,
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
    inference(superposition,[status(thm)],[c_5754,c_5800])).

cnf(c_5819,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5806,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68])).

cnf(c_38,negated_conjecture,
    ( v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_59,plain,
    ( v1_borsuk_1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,negated_conjecture,
    ( v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_56,plain,
    ( v1_borsuk_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12735,c_8597,c_6343,c_6315,c_6282,c_5819,c_68,c_66,c_65,c_64,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_53,c_52,c_51,c_50,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:25:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.49/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.50  
% 7.49/1.50  ------  iProver source info
% 7.49/1.50  
% 7.49/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.50  git: non_committed_changes: false
% 7.49/1.50  git: last_make_outside_of_git: false
% 7.49/1.50  
% 7.49/1.50  ------ 
% 7.49/1.50  ------ Parsing...
% 7.49/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  ------ Proving...
% 7.49/1.50  ------ Problem Properties 
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  clauses                                 46
% 7.49/1.50  conjectures                             22
% 7.49/1.50  EPR                                     18
% 7.49/1.50  Horn                                    39
% 7.49/1.50  unary                                   21
% 7.49/1.50  binary                                  9
% 7.49/1.50  lits                                    181
% 7.49/1.50  lits eq                                 3
% 7.49/1.50  fd_pure                                 0
% 7.49/1.50  fd_pseudo                               0
% 7.49/1.50  fd_cond                                 0
% 7.49/1.50  fd_pseudo_cond                          0
% 7.49/1.50  AC symbols                              0
% 7.49/1.50  
% 7.49/1.50  ------ Input Options Time Limit: Unbounded
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing...
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.49/1.50  Current options:
% 7.49/1.50  ------ 
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 34 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing...
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 41 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing...
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 46 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing...
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 46 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.49/1.50  
% 7.49/1.50  ------ Proving...
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  % SZS status Theorem for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  fof(f7,conjecture,(
% 7.49/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f8,negated_conjecture,(
% 7.49/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 7.49/1.50    inference(negated_conjecture,[],[f7])).
% 7.49/1.50  
% 7.49/1.50  fof(f20,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f8])).
% 7.49/1.50  
% 7.49/1.50  fof(f21,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f20])).
% 7.49/1.50  
% 7.49/1.50  fof(f37,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),sK7) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK7,X3,X1) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f36,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),sK6) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK6,X2,X1) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f35,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5))) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X4) & k1_tsep_1(X0,X2,sK5) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(X5,sK5,X1) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & v1_borsuk_1(sK5,X0) & ~v2_struct_0(sK5))) )),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f34,plain,(
% 7.49/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X4) & k1_tsep_1(X0,sK4,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(X4,sK4,X1) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & v1_borsuk_1(sK4,X0) & ~v2_struct_0(sK4))) )),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f33,plain,(
% 7.49/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),X0,sK3) | ~v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f32,plain,(
% 7.49/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(sK2,X2,X3) = sK2 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_borsuk_1(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.49/1.50    introduced(choice_axiom,[])).
% 7.49/1.50  
% 7.49/1.50  fof(f38,plain,(
% 7.49/1.50    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) & k1_tsep_1(sK2,sK4,sK5) = sK2 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & v1_borsuk_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & v1_borsuk_1(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.49/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f21,f37,f36,f35,f34,f33,f32])).
% 7.49/1.50  
% 7.49/1.50  fof(f84,plain,(
% 7.49/1.50    k1_tsep_1(sK2,sK4,sK5) = sK2),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f2,axiom,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f11,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f2])).
% 7.49/1.50  
% 7.49/1.50  fof(f12,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f11])).
% 7.49/1.50  
% 7.49/1.50  fof(f42,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f12])).
% 7.49/1.50  
% 7.49/1.50  fof(f64,plain,(
% 7.49/1.50    ~v2_struct_0(sK2)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f65,plain,(
% 7.49/1.50    v2_pre_topc(sK2)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f66,plain,(
% 7.49/1.50    l1_pre_topc(sK2)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f70,plain,(
% 7.49/1.50    ~v2_struct_0(sK4)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f72,plain,(
% 7.49/1.50    m1_pre_topc(sK4,sK2)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f73,plain,(
% 7.49/1.50    ~v2_struct_0(sK5)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f75,plain,(
% 7.49/1.50    m1_pre_topc(sK5,sK2)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f43,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f12])).
% 7.49/1.50  
% 7.49/1.50  fof(f3,axiom,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f13,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f3])).
% 7.49/1.50  
% 7.49/1.50  fof(f14,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f13])).
% 7.49/1.50  
% 7.49/1.50  fof(f44,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f14])).
% 7.49/1.50  
% 7.49/1.50  fof(f45,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f14])).
% 7.49/1.50  
% 7.49/1.50  fof(f46,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f14])).
% 7.49/1.50  
% 7.49/1.50  fof(f1,axiom,(
% 7.49/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f9,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.49/1.50    inference(ennf_transformation,[],[f1])).
% 7.49/1.50  
% 7.49/1.50  fof(f10,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.49/1.50    inference(flattening,[],[f9])).
% 7.49/1.50  
% 7.49/1.50  fof(f25,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.49/1.50    inference(nnf_transformation,[],[f10])).
% 7.49/1.50  
% 7.49/1.50  fof(f39,plain,(
% 7.49/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f25])).
% 7.49/1.50  
% 7.49/1.50  fof(f86,plain,(
% 7.49/1.50    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f80,plain,(
% 7.49/1.50    v1_funct_1(sK7)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f81,plain,(
% 7.49/1.50    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f83,plain,(
% 7.49/1.50    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f67,plain,(
% 7.49/1.50    ~v2_struct_0(sK3)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f68,plain,(
% 7.49/1.50    v2_pre_topc(sK3)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f69,plain,(
% 7.49/1.50    l1_pre_topc(sK3)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f76,plain,(
% 7.49/1.50    v1_funct_1(sK6)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f77,plain,(
% 7.49/1.50    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f5,axiom,(
% 7.49/1.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f17,plain,(
% 7.49/1.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.49/1.50    inference(ennf_transformation,[],[f5])).
% 7.49/1.50  
% 7.49/1.50  fof(f62,plain,(
% 7.49/1.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f17])).
% 7.49/1.50  
% 7.49/1.50  fof(f79,plain,(
% 7.49/1.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f41,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f12])).
% 7.49/1.50  
% 7.49/1.50  fof(f22,plain,(
% 7.49/1.50    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 7.49/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.49/1.50  
% 7.49/1.50  fof(f29,plain,(
% 7.49/1.50    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 7.49/1.50    inference(nnf_transformation,[],[f22])).
% 7.49/1.50  
% 7.49/1.50  fof(f30,plain,(
% 7.49/1.50    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 7.49/1.50    inference(flattening,[],[f29])).
% 7.49/1.50  
% 7.49/1.50  fof(f31,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.49/1.50    inference(rectify,[],[f30])).
% 7.49/1.50  
% 7.49/1.50  fof(f60,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 7.49/1.50    inference(cnf_transformation,[],[f31])).
% 7.49/1.50  
% 7.49/1.50  fof(f85,plain,(
% 7.49/1.50    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f53,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f31])).
% 7.49/1.50  
% 7.49/1.50  fof(f78,plain,(
% 7.49/1.50    v5_pre_topc(sK6,sK4,sK3)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f82,plain,(
% 7.49/1.50    v5_pre_topc(sK7,sK5,sK3)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f23,plain,(
% 7.49/1.50    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 7.49/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.49/1.50  
% 7.49/1.50  fof(f26,plain,(
% 7.49/1.50    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 7.49/1.50    inference(nnf_transformation,[],[f23])).
% 7.49/1.50  
% 7.49/1.50  fof(f27,plain,(
% 7.49/1.50    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 7.49/1.50    inference(flattening,[],[f26])).
% 7.49/1.50  
% 7.49/1.50  fof(f28,plain,(
% 7.49/1.50    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 7.49/1.50    inference(rectify,[],[f27])).
% 7.49/1.50  
% 7.49/1.50  fof(f50,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f28])).
% 7.49/1.50  
% 7.49/1.50  fof(f4,axiom,(
% 7.49/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f15,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f4])).
% 7.49/1.50  
% 7.49/1.50  fof(f16,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f15])).
% 7.49/1.50  
% 7.49/1.50  fof(f24,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(definition_folding,[],[f16,f23,f22])).
% 7.49/1.50  
% 7.49/1.50  fof(f61,plain,(
% 7.49/1.50    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f24])).
% 7.49/1.50  
% 7.49/1.50  fof(f6,axiom,(
% 7.49/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 7.49/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.50  
% 7.49/1.50  fof(f18,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.50    inference(ennf_transformation,[],[f6])).
% 7.49/1.50  
% 7.49/1.50  fof(f19,plain,(
% 7.49/1.50    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.50    inference(flattening,[],[f18])).
% 7.49/1.50  
% 7.49/1.50  fof(f63,plain,(
% 7.49/1.50    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.50    inference(cnf_transformation,[],[f19])).
% 7.49/1.50  
% 7.49/1.50  fof(f87,plain,(
% 7.49/1.50    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f74,plain,(
% 7.49/1.50    v1_borsuk_1(sK5,sK2)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  fof(f71,plain,(
% 7.49/1.50    v1_borsuk_1(sK4,sK2)),
% 7.49/1.50    inference(cnf_transformation,[],[f38])).
% 7.49/1.50  
% 7.49/1.50  cnf(c_28,negated_conjecture,
% 7.49/1.50      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 7.49/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1996,negated_conjecture,
% 7.49/1.50      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_28]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X1,X5)
% 7.49/1.50      | ~ m1_pre_topc(X4,X5)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X5)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X5)
% 7.49/1.50      | v2_struct_0(X5)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_funct_1(X3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2017,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 7.49/1.50      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))
% 7.49/1.50      | ~ m1_pre_topc(X2_55,X3_55)
% 7.49/1.50      | ~ m1_pre_topc(X0_55,X3_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ v2_pre_topc(X3_55)
% 7.49/1.50      | ~ v2_pre_topc(X1_55)
% 7.49/1.50      | ~ l1_pre_topc(X3_55)
% 7.49/1.50      | ~ l1_pre_topc(X1_55)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(X3_55)
% 7.49/1.50      | v2_struct_0(X2_55)
% 7.49/1.50      | ~ v1_funct_1(X0_53)
% 7.49/1.50      | ~ v1_funct_1(X1_53) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5037,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)) = iProver_top
% 7.49/1.50      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2017]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5657,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1996,c_5037]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_48,negated_conjecture,
% 7.49/1.50      ( ~ v2_struct_0(sK2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_49,plain,
% 7.49/1.50      ( v2_struct_0(sK2) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_47,negated_conjecture,
% 7.49/1.50      ( v2_pre_topc(sK2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_50,plain,
% 7.49/1.50      ( v2_pre_topc(sK2) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_46,negated_conjecture,
% 7.49/1.50      ( l1_pre_topc(sK2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_51,plain,
% 7.49/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_42,negated_conjecture,
% 7.49/1.50      ( ~ v2_struct_0(sK4) ),
% 7.49/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_55,plain,
% 7.49/1.50      ( v2_struct_0(sK4) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_40,negated_conjecture,
% 7.49/1.50      ( m1_pre_topc(sK4,sK2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_57,plain,
% 7.49/1.50      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_39,negated_conjecture,
% 7.49/1.50      ( ~ v2_struct_0(sK5) ),
% 7.49/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_58,plain,
% 7.49/1.50      ( v2_struct_0(sK5) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_37,negated_conjecture,
% 7.49/1.50      ( m1_pre_topc(sK5,sK2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_60,plain,
% 7.49/1.50      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5753,plain,
% 7.49/1.50      ( v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_5657,c_49,c_50,c_51,c_55,c_57,c_58,c_60]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5754,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) = iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_5753]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X1,X5)
% 7.49/1.50      | ~ m1_pre_topc(X4,X5)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X5)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X5)
% 7.49/1.50      | v2_struct_0(X5)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_funct_1(X3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2018,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 7.49/1.50      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 7.49/1.50      | ~ m1_pre_topc(X2_55,X3_55)
% 7.49/1.50      | ~ m1_pre_topc(X0_55,X3_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ v2_pre_topc(X3_55)
% 7.49/1.50      | ~ v2_pre_topc(X1_55)
% 7.49/1.50      | ~ l1_pre_topc(X3_55)
% 7.49/1.50      | ~ l1_pre_topc(X1_55)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(X3_55)
% 7.49/1.50      | v2_struct_0(X2_55)
% 7.49/1.50      | ~ v1_funct_1(X0_53)
% 7.49/1.50      | ~ v1_funct_1(X1_53) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5036,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)))) = iProver_top
% 7.49/1.50      | v2_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2018]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5546,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1996,c_5036]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5775,plain,
% 7.49/1.50      ( v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_5546,c_49,c_50,c_51,c_55,c_57,c_58,c_60]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5776,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) = iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_5775]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X3,X4)
% 7.49/1.50      | ~ m1_pre_topc(X1,X4)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2013,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 7.49/1.50      | ~ m1_pre_topc(X2_55,X3_55)
% 7.49/1.50      | ~ m1_pre_topc(X0_55,X3_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ v2_pre_topc(X3_55)
% 7.49/1.50      | ~ v2_pre_topc(X1_55)
% 7.49/1.50      | ~ l1_pre_topc(X3_55)
% 7.49/1.50      | ~ l1_pre_topc(X1_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(X3_55)
% 7.49/1.50      | ~ v1_funct_1(X0_53)
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5041,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2013]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7866,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53),u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,X2_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X2_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X2_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5776,c_5041]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11780,plain,
% 7.49/1.50      ( v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,X2_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X2_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X2_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_7866,c_49,c_50,c_51,c_55,c_57,c_58,c_60,c_5657]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11781,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,X2_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X2_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X2_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X2_55,X0_55,sK2,X1_55,k10_tmap_1(sK2,X0_55,sK4,sK5,X1_53,X0_53))) = iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_11780]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X4,X3)
% 7.49/1.50      | ~ m1_pre_topc(X1,X3)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X3)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X3)
% 7.49/1.50      | v2_struct_0(X3)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | ~ v1_funct_1(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2014,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_53),u1_struct_0(X3_55),u1_struct_0(X1_55))
% 7.49/1.50      | ~ m1_pre_topc(X3_55,X2_55)
% 7.49/1.50      | ~ m1_pre_topc(X0_55,X2_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ v2_pre_topc(X2_55)
% 7.49/1.50      | ~ v2_pre_topc(X1_55)
% 7.49/1.50      | ~ l1_pre_topc(X2_55)
% 7.49/1.50      | ~ l1_pre_topc(X1_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(X2_55)
% 7.49/1.50      | ~ v1_funct_1(X0_53) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5040,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_53),u1_struct_0(X3_55),u1_struct_0(X1_55)) = iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(X3_55,X2_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X2_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X2_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2014]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X3,X4)
% 7.49/1.50      | ~ m1_pre_topc(X1,X4)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | ~ v1_funct_1(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2015,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 7.49/1.50      | ~ m1_pre_topc(X2_55,X3_55)
% 7.49/1.50      | ~ m1_pre_topc(X0_55,X3_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ v2_pre_topc(X3_55)
% 7.49/1.50      | ~ v2_pre_topc(X1_55)
% 7.49/1.50      | ~ l1_pre_topc(X3_55)
% 7.49/1.50      | ~ l1_pre_topc(X1_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(X3_55)
% 7.49/1.50      | ~ v1_funct_1(X0_53) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5039,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
% 7.49/1.50      | v2_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1,plain,
% 7.49/1.50      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.49/1.50      | ~ v1_funct_2(X3,X0,X1)
% 7.49/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | ~ v1_funct_1(X2)
% 7.49/1.50      | X2 = X3 ),
% 7.49/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_26,negated_conjecture,
% 7.49/1.50      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
% 7.49/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_560,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.50      | ~ v1_funct_2(X3,X1,X2)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | X3 = X0
% 7.49/1.50      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 7.49/1.50      | u1_struct_0(sK5) != X1
% 7.49/1.50      | u1_struct_0(sK3) != X2
% 7.49/1.50      | sK7 != X3 ),
% 7.49/1.50      inference(resolution_lifted,[status(thm)],[c_1,c_26]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_561,plain,
% 7.49/1.50      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.49/1.50      | ~ v1_funct_1(sK7)
% 7.49/1.50      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(unflattening,[status(thm)],[c_560]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_32,negated_conjecture,
% 7.49/1.50      ( v1_funct_1(sK7) ),
% 7.49/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_31,negated_conjecture,
% 7.49/1.50      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_29,negated_conjecture,
% 7.49/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_563,plain,
% 7.49/1.50      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.49/1.50      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_561,c_32,c_31,c_29]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_564,plain,
% 7.49/1.50      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.49/1.50      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_563]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1974,plain,
% 7.49/1.50      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.49/1.50      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_564]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5058,plain,
% 7.49/1.50      ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5244,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_5058,c_1996]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6679,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5039,c_5244]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_45,negated_conjecture,
% 7.49/1.50      ( ~ v2_struct_0(sK3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_52,plain,
% 7.49/1.50      ( v2_struct_0(sK3) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_44,negated_conjecture,
% 7.49/1.50      ( v2_pre_topc(sK3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_53,plain,
% 7.49/1.50      ( v2_pre_topc(sK3) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_43,negated_conjecture,
% 7.49/1.50      ( l1_pre_topc(sK3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_54,plain,
% 7.49/1.50      ( l1_pre_topc(sK3) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_36,negated_conjecture,
% 7.49/1.50      ( v1_funct_1(sK6) ),
% 7.49/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_61,plain,
% 7.49/1.50      ( v1_funct_1(sK6) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_35,negated_conjecture,
% 7.49/1.50      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_62,plain,
% 7.49/1.50      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_23,plain,
% 7.49/1.50      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_75,plain,
% 7.49/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 7.49/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_77,plain,
% 7.49/1.50      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_75]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_33,negated_conjecture,
% 7.49/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 7.49/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1991,negated_conjecture,
% 7.49/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_33]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5075,plain,
% 7.49/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1991]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1995,negated_conjecture,
% 7.49/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_29]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5079,plain,
% 7.49/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1995]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.50      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.49/1.50      | ~ m1_pre_topc(X1,X5)
% 7.49/1.50      | ~ m1_pre_topc(X4,X5)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.49/1.50      | ~ v2_pre_topc(X2)
% 7.49/1.50      | ~ v2_pre_topc(X5)
% 7.49/1.50      | ~ l1_pre_topc(X2)
% 7.49/1.50      | ~ l1_pre_topc(X5)
% 7.49/1.50      | v2_struct_0(X5)
% 7.49/1.50      | v2_struct_0(X2)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2016,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 7.49/1.50      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 7.49/1.50      | ~ m1_pre_topc(X2_55,X3_55)
% 7.49/1.50      | ~ m1_pre_topc(X0_55,X3_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 7.49/1.50      | ~ v2_pre_topc(X3_55)
% 7.49/1.50      | ~ v2_pre_topc(X1_55)
% 7.49/1.50      | ~ l1_pre_topc(X3_55)
% 7.49/1.50      | ~ l1_pre_topc(X1_55)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(X3_55)
% 7.49/1.50      | v2_struct_0(X2_55)
% 7.49/1.50      | ~ v1_funct_1(X0_53)
% 7.49/1.50      | ~ v1_funct_1(X1_53)
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5038,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X3_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X3_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X2_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2016]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5870,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,X1_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5079,c_5038]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_65,plain,
% 7.49/1.50      ( v1_funct_1(sK7) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_66,plain,
% 7.49/1.50      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6138,plain,
% 7.49/1.50      ( v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,X1_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 7.49/1.50      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_5870,c_52,c_53,c_54,c_58,c_65,c_66]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6139,plain,
% 7.49/1.50      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,X1_55) != iProver_top
% 7.49/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X1_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(X1_55) = iProver_top
% 7.49/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7)) = iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_6138]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6155,plain,
% 7.49/1.50      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,X0_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5075,c_6139]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6282,plain,
% 7.49/1.50      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_6155]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6960,plain,
% 7.49/1.50      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_6679,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,
% 7.49/1.50                 c_61,c_62,c_77,c_6282]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6961,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_6960]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7128,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5040,c_6961]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12199,plain,
% 7.49/1.50      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_7128,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,
% 7.49/1.50                 c_61,c_62,c_77,c_6282]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12200,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_12199]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12207,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5776,c_12200]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_64,plain,
% 7.49/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_68,plain,
% 7.49/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12240,plain,
% 7.49/1.50      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_12207,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12241,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_12240]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12248,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_11781,c_12241]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12458,plain,
% 7.49/1.50      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_12248,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,
% 7.49/1.50                 c_61,c_62,c_64,c_65,c_66,c_68,c_77,c_6282]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12459,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_12458]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12464,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5754,c_12459]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12469,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_12464,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_13,plain,
% 7.49/1.50      ( sP0(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 7.49/1.50      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 7.49/1.50      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 7.49/1.50      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2007,plain,
% 7.49/1.50      ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55)
% 7.49/1.50      | ~ v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),X1_55,X0_55)
% 7.49/1.50      | ~ v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),X2_55,X0_55)
% 7.49/1.50      | ~ v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X0_55))
% 7.49/1.50      | ~ v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55))))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X0_55))))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5047,plain,
% 7.49/1.50      ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),X1_55,X0_55) != iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),X2_55,X0_55) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),u1_struct_0(X1_55),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X1_55,X0_53)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53)) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2007]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_10244,plain,
% 7.49/1.50      ( sP0(X0_55,sK5,X0_53,sK4,sK2) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),sK5,X0_55) != iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),sK4,X0_55) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_53)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_53)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1996,c_5047]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_10254,plain,
% 7.49/1.50      ( sP0(X0_55,sK5,X0_53,sK4,sK2) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),sK5,X0_55) != iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),sK4,X0_55) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,X0_55,sK2,sK5,X0_53)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53)) != iProver_top ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_10244,c_1996]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12474,plain,
% 7.49/1.50      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
% 7.49/1.50      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12469,c_10254]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_27,negated_conjecture,
% 7.49/1.50      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
% 7.49/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_580,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.50      | ~ v1_funct_2(X3,X1,X2)
% 7.49/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.50      | ~ v1_funct_1(X0)
% 7.49/1.50      | ~ v1_funct_1(X3)
% 7.49/1.50      | X3 = X0
% 7.49/1.50      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 7.49/1.50      | u1_struct_0(sK4) != X1
% 7.49/1.50      | u1_struct_0(sK3) != X2
% 7.49/1.50      | sK6 != X3 ),
% 7.49/1.50      inference(resolution_lifted,[status(thm)],[c_1,c_27]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_581,plain,
% 7.49/1.50      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 7.49/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.49/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.49/1.50      | ~ v1_funct_1(sK6)
% 7.49/1.50      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(unflattening,[status(thm)],[c_580]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_583,plain,
% 7.49/1.50      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.49/1.50      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.49/1.50      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_581,c_36,c_35,c_33]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_584,plain,
% 7.49/1.50      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.49/1.50      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_583]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1973,plain,
% 7.49/1.50      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.49/1.50      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_584]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5059,plain,
% 7.49/1.50      ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1973]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5253,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(light_normalisation,[status(thm)],[c_5059,c_1996]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6680,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5039,c_5253]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6993,plain,
% 7.49/1.50      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_6680,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,
% 7.49/1.50                 c_61,c_62,c_77,c_6282]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6994,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_6993]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7129,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5040,c_6994]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20,plain,
% 7.49/1.50      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2000,plain,
% 7.49/1.50      ( ~ sP0(X0_55,X1_55,X0_53,X2_55,X3_55)
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_20]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5054,plain,
% 7.49/1.50      ( sP0(X0_55,X1_55,X0_53,X2_55,X3_55) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(X3_55,X0_55,k1_tsep_1(X3_55,X2_55,X1_55),X2_55,X0_53),u1_struct_0(X2_55),u1_struct_0(X0_55)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2000]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7232,plain,
% 7.49/1.50      ( sP0(X0_55,sK5,X0_53,sK4,sK2) != iProver_top
% 7.49/1.50      | v1_funct_2(k3_tmap_1(sK2,X0_55,sK2,sK4,X0_53),u1_struct_0(sK4),u1_struct_0(X0_55)) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1996,c_5054]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7284,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_7232,c_6994]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7558,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_7284,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,
% 7.49/1.50                 c_61,c_62,c_77,c_6282,c_7129]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7566,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5776,c_7558]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7673,plain,
% 7.49/1.50      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_7566,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7674,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_7673]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_11802,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_11781,c_7674]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12306,plain,
% 7.49/1.50      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_7129,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_57,c_60,
% 7.49/1.50                 c_61,c_62,c_64,c_65,c_66,c_68,c_77,c_6282,c_11802]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12307,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_12306]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12312,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5754,c_12307]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12331,plain,
% 7.49/1.50      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_12312,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12568,plain,
% 7.49/1.50      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 7.49/1.50      | v5_pre_topc(sK7,sK5,sK3) != iProver_top
% 7.49/1.50      | v5_pre_topc(sK6,sK4,sK3) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(light_normalisation,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_12474,c_12331,c_12469]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_34,negated_conjecture,
% 7.49/1.50      ( v5_pre_topc(sK6,sK4,sK3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_63,plain,
% 7.49/1.50      ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_30,negated_conjecture,
% 7.49/1.50      ( v5_pre_topc(sK7,sK5,sK3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_67,plain,
% 7.49/1.50      ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12729,plain,
% 7.49/1.50      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_12568,c_61,c_62,c_63,c_64,c_65,c_66,c_67,c_68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_9,plain,
% 7.49/1.50      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ sP0(X4,X3,X2,X1,X0)
% 7.49/1.50      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 7.49/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2011,plain,
% 7.49/1.50      ( ~ sP1(X0_55,X1_55,X0_53,X2_55,X3_55)
% 7.49/1.50      | ~ sP0(X3_55,X2_55,X0_53,X1_55,X0_55)
% 7.49/1.50      | v5_pre_topc(X0_53,k1_tsep_1(X0_55,X1_55,X2_55),X3_55) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5043,plain,
% 7.49/1.50      ( sP1(X0_55,X1_55,X0_53,X2_55,X3_55) != iProver_top
% 7.49/1.50      | sP0(X3_55,X2_55,X0_53,X1_55,X0_55) != iProver_top
% 7.49/1.50      | v5_pre_topc(X0_53,k1_tsep_1(X0_55,X1_55,X2_55),X3_55) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_2011]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8402,plain,
% 7.49/1.50      ( sP1(sK2,sK4,X0_53,sK5,X0_55) != iProver_top
% 7.49/1.50      | sP0(X0_55,sK5,X0_53,sK4,sK2) != iProver_top
% 7.49/1.50      | v5_pre_topc(X0_53,sK2,X0_55) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_1996,c_5043]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12735,plain,
% 7.49/1.50      ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_12729,c_8402]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_22,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ r4_tsep_1(X0,X1,X3)
% 7.49/1.50      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 7.49/1.50      | ~ m1_pre_topc(X3,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X3)
% 7.49/1.50      | ~ v1_funct_1(X2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_24,plain,
% 7.49/1.50      ( r4_tsep_1(X0,X1,X2)
% 7.49/1.50      | ~ v1_borsuk_1(X2,X0)
% 7.49/1.50      | ~ v1_borsuk_1(X1,X0)
% 7.49/1.50      | ~ m1_pre_topc(X2,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | v2_struct_0(X0) ),
% 7.49/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_503,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 7.49/1.50      | ~ v1_borsuk_1(X5,X6)
% 7.49/1.50      | ~ v1_borsuk_1(X7,X6)
% 7.49/1.50      | ~ m1_pre_topc(X3,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ m1_pre_topc(X5,X6)
% 7.49/1.50      | ~ m1_pre_topc(X7,X6)
% 7.49/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ v2_pre_topc(X6)
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X6)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X3)
% 7.49/1.50      | v2_struct_0(X6)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | ~ v1_funct_1(X2)
% 7.49/1.50      | X5 != X3
% 7.49/1.50      | X7 != X1
% 7.49/1.50      | X6 != X0 ),
% 7.49/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_24]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_504,plain,
% 7.49/1.50      ( sP1(X0,X1,X2,X3,X4)
% 7.49/1.50      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 7.49/1.50      | ~ v1_borsuk_1(X3,X0)
% 7.49/1.50      | ~ v1_borsuk_1(X1,X0)
% 7.49/1.50      | ~ m1_pre_topc(X3,X0)
% 7.49/1.50      | ~ m1_pre_topc(X1,X0)
% 7.49/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 7.49/1.50      | ~ v2_pre_topc(X0)
% 7.49/1.50      | ~ v2_pre_topc(X4)
% 7.49/1.50      | ~ l1_pre_topc(X0)
% 7.49/1.50      | ~ l1_pre_topc(X4)
% 7.49/1.50      | v2_struct_0(X0)
% 7.49/1.50      | v2_struct_0(X1)
% 7.49/1.50      | v2_struct_0(X3)
% 7.49/1.50      | v2_struct_0(X4)
% 7.49/1.50      | ~ v1_funct_1(X2) ),
% 7.49/1.50      inference(unflattening,[status(thm)],[c_503]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1975,plain,
% 7.49/1.50      ( sP1(X0_55,X1_55,X0_53,X2_55,X3_55)
% 7.49/1.50      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55))
% 7.49/1.50      | ~ v1_borsuk_1(X1_55,X0_55)
% 7.49/1.50      | ~ v1_borsuk_1(X2_55,X0_55)
% 7.49/1.50      | ~ m1_pre_topc(X1_55,X0_55)
% 7.49/1.50      | ~ m1_pre_topc(X2_55,X0_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55))))
% 7.49/1.50      | ~ v2_pre_topc(X0_55)
% 7.49/1.50      | ~ v2_pre_topc(X3_55)
% 7.49/1.50      | ~ l1_pre_topc(X0_55)
% 7.49/1.50      | ~ l1_pre_topc(X3_55)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(X3_55)
% 7.49/1.50      | v2_struct_0(X2_55)
% 7.49/1.50      | ~ v1_funct_1(X0_53) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_504]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8589,plain,
% 7.49/1.50      ( sP1(X0_55,sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
% 7.49/1.50      | ~ v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))
% 7.49/1.50      | ~ v1_borsuk_1(sK5,X0_55)
% 7.49/1.50      | ~ v1_borsuk_1(sK4,X0_55)
% 7.49/1.50      | ~ m1_pre_topc(sK5,X0_55)
% 7.49/1.50      | ~ m1_pre_topc(sK4,X0_55)
% 7.49/1.50      | ~ m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v2_pre_topc(X0_55)
% 7.49/1.50      | ~ v2_pre_topc(sK3)
% 7.49/1.50      | ~ l1_pre_topc(X0_55)
% 7.49/1.50      | ~ l1_pre_topc(sK3)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(sK5)
% 7.49/1.50      | v2_struct_0(sK4)
% 7.49/1.50      | v2_struct_0(sK3)
% 7.49/1.50      | ~ v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1975]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8595,plain,
% 7.49/1.50      ( sP1(X0_55,sK4,k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_borsuk_1(sK5,X0_55) != iProver_top
% 7.49/1.50      | v1_borsuk_1(sK4,X0_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,X0_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,X0_55) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_8589]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8597,plain,
% 7.49/1.50      ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_borsuk_1(sK5,sK2) != iProver_top
% 7.49/1.50      | v1_borsuk_1(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_8595]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5662,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3))
% 7.49/1.50      | v1_funct_2(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7),u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))
% 7.49/1.50      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_pre_topc(X0_55,X1_55)
% 7.49/1.50      | ~ m1_pre_topc(sK5,X1_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 7.49/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v2_pre_topc(X1_55)
% 7.49/1.50      | ~ v2_pre_topc(sK3)
% 7.49/1.50      | ~ l1_pre_topc(X1_55)
% 7.49/1.50      | ~ l1_pre_topc(sK3)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(sK5)
% 7.49/1.50      | v2_struct_0(sK3)
% 7.49/1.50      | ~ v1_funct_1(X0_53)
% 7.49/1.50      | ~ v1_funct_1(sK7) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_2017]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6340,plain,
% 7.49/1.50      ( v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))
% 7.49/1.50      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_pre_topc(sK5,X0_55)
% 7.49/1.50      | ~ m1_pre_topc(sK4,X0_55)
% 7.49/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v2_pre_topc(X0_55)
% 7.49/1.50      | ~ v2_pre_topc(sK3)
% 7.49/1.50      | ~ l1_pre_topc(X0_55)
% 7.49/1.50      | ~ l1_pre_topc(sK3)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(sK5)
% 7.49/1.50      | v2_struct_0(sK4)
% 7.49/1.50      | v2_struct_0(sK3)
% 7.49/1.50      | ~ v1_funct_1(sK7)
% 7.49/1.50      | ~ v1_funct_1(sK6) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_5662]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6341,plain,
% 7.49/1.50      ( v1_funct_2(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,X0_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,X0_55) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_6340]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6343,plain,
% 7.49/1.50      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_6341]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5661,plain,
% 7.49/1.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(sK3))
% 7.49/1.50      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_pre_topc(X0_55,X1_55)
% 7.49/1.50      | ~ m1_pre_topc(sK5,X1_55)
% 7.49/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_53,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))))
% 7.49/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v2_pre_topc(X1_55)
% 7.49/1.50      | ~ v2_pre_topc(sK3)
% 7.49/1.50      | ~ l1_pre_topc(X1_55)
% 7.49/1.50      | ~ l1_pre_topc(sK3)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(X1_55)
% 7.49/1.50      | v2_struct_0(sK5)
% 7.49/1.50      | v2_struct_0(sK3)
% 7.49/1.50      | ~ v1_funct_1(X0_53)
% 7.49/1.50      | ~ v1_funct_1(sK7) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_2018]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6312,plain,
% 7.49/1.50      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.49/1.50      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_pre_topc(sK5,X0_55)
% 7.49/1.50      | ~ m1_pre_topc(sK4,X0_55)
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3))))
% 7.49/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.49/1.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v2_pre_topc(X0_55)
% 7.49/1.50      | ~ v2_pre_topc(sK3)
% 7.49/1.50      | ~ l1_pre_topc(X0_55)
% 7.49/1.50      | ~ l1_pre_topc(sK3)
% 7.49/1.50      | v2_struct_0(X0_55)
% 7.49/1.50      | v2_struct_0(sK5)
% 7.49/1.50      | v2_struct_0(sK4)
% 7.49/1.50      | v2_struct_0(sK3)
% 7.49/1.50      | ~ v1_funct_1(sK7)
% 7.49/1.50      | ~ v1_funct_1(sK6) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_5661]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6313,plain,
% 7.49/1.50      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,X0_55) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,X0_55) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(X0_55,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_55,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(X0_55) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(X0_55) = iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_6312]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6315,plain,
% 7.49/1.50      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.49/1.50      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.50      | v2_struct_0(sK5) = iProver_top
% 7.49/1.50      | v2_struct_0(sK4) = iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v2_struct_0(sK2) = iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_6313]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_25,negated_conjecture,
% 7.49/1.50      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 7.49/1.50      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1997,negated_conjecture,
% 7.49/1.50      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 7.49/1.50      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 7.49/1.50      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.49/1.50      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.49/1.50      inference(subtyping,[status(esa)],[c_25]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5080,plain,
% 7.49/1.50      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_1997]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5791,plain,
% 7.49/1.50      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5776,c_5080]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5799,plain,
% 7.49/1.50      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_5791,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5800,plain,
% 7.49/1.50      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.49/1.50      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_5799]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5806,plain,
% 7.49/1.50      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.49/1.50      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.49/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.49/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.49/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.49/1.50      | v2_struct_0(sK3) = iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.49/1.50      | v1_funct_1(sK7) != iProver_top
% 7.49/1.50      | v1_funct_1(sK6) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_5754,c_5800]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5819,plain,
% 7.49/1.50      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.49/1.50      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_5806,c_52,c_53,c_54,c_61,c_62,c_64,c_65,c_66,c_68]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_38,negated_conjecture,
% 7.49/1.50      ( v1_borsuk_1(sK5,sK2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_59,plain,
% 7.49/1.50      ( v1_borsuk_1(sK5,sK2) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_41,negated_conjecture,
% 7.49/1.50      ( v1_borsuk_1(sK4,sK2) ),
% 7.49/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_56,plain,
% 7.49/1.50      ( v1_borsuk_1(sK4,sK2) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(contradiction,plain,
% 7.49/1.50      ( $false ),
% 7.49/1.50      inference(minisat,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_12735,c_8597,c_6343,c_6315,c_6282,c_5819,c_68,c_66,
% 7.49/1.50                 c_65,c_64,c_62,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,
% 7.49/1.50                 c_53,c_52,c_51,c_50,c_49]) ).
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  ------                               Statistics
% 7.49/1.50  
% 7.49/1.50  ------ Selected
% 7.49/1.50  
% 7.49/1.50  total_time:                             0.506
% 7.49/1.50  
%------------------------------------------------------------------------------

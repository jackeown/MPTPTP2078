%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:28 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  236 (7192 expanded)
%              Number of clauses        :  165 (1324 expanded)
%              Number of leaves         :   14 (3345 expanded)
%              Depth                    :   32
%              Number of atoms          : 1970 (180906 expanded)
%              Number of equality atoms :  735 (11010 expanded)
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

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f18,f34,f33,f32,f31,f30,f29])).

fof(f80,plain,(
    k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f35])).

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
    inference(ennf_transformation,[],[f2])).

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

fof(f39,plain,(
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

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f40,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f12])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f13])).

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

fof(f8,plain,(
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
    inference(flattening,[],[f8])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f38,plain,(
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

fof(f19,plain,(
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

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f14])).

fof(f21,plain,(
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
    inference(definition_folding,[],[f15,f20,f19])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_27,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1929,negated_conjecture,
    ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
    inference(subtyping,[status(esa)],[c_27])).

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
    inference(cnf_transformation,[],[f39])).

cnf(c_1951,plain,
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

cnf(c_4971,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(c_5591,plain,
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
    inference(superposition,[status(thm)],[c_1929,c_4971])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_48,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_49,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_50,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_54,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_56,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_57,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_59,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5687,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5591,c_48,c_49,c_50,c_54,c_56,c_57,c_59])).

cnf(c_5688,plain,
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
    inference(renaming,[status(thm)],[c_5687])).

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
    inference(cnf_transformation,[],[f40])).

cnf(c_1952,plain,
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

cnf(c_4970,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1952])).

cnf(c_5480,plain,
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
    inference(superposition,[status(thm)],[c_1929,c_4970])).

cnf(c_5709,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5480,c_48,c_49,c_50,c_54,c_56,c_57,c_59])).

cnf(c_5710,plain,
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
    inference(renaming,[status(thm)],[c_5709])).

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
    inference(cnf_transformation,[],[f41])).

cnf(c_1947,plain,
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
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_4975,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1947])).

cnf(c_7800,plain,
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
    inference(superposition,[status(thm)],[c_5710,c_4975])).

cnf(c_11724,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_7800,c_48,c_49,c_50,c_54,c_56,c_57,c_59,c_5591])).

cnf(c_11725,plain,
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
    inference(renaming,[status(thm)],[c_11724])).

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
    inference(cnf_transformation,[],[f42])).

cnf(c_1948,plain,
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
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_4974,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1948])).

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
    inference(cnf_transformation,[],[f43])).

cnf(c_1949,plain,
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
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4973,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_25,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_494,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1,c_25])).

cnf(c_495,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_497,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_31,c_30,c_28])).

cnf(c_498,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_1908,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_498])).

cnf(c_4992,plain,
    ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1908])).

cnf(c_5178,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4992,c_1929])).

cnf(c_6613,plain,
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
    inference(superposition,[status(thm)],[c_4973,c_5178])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_51,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_52,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_53,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_60,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_61,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_23,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_71,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_73,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1924,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_5009,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_1928,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_5013,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1928])).

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
    inference(cnf_transformation,[],[f38])).

cnf(c_1950,plain,
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

cnf(c_4972,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1950])).

cnf(c_5804,plain,
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
    inference(superposition,[status(thm)],[c_5013,c_4972])).

cnf(c_64,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_65,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6072,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5804,c_51,c_52,c_53,c_57,c_64,c_65])).

cnf(c_6073,plain,
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
    inference(renaming,[status(thm)],[c_6072])).

cnf(c_6089,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5009,c_6073])).

cnf(c_6216,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6089])).

cnf(c_6894,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6613,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,c_60,c_61,c_73,c_6216])).

cnf(c_6895,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6894])).

cnf(c_7062,plain,
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
    inference(superposition,[status(thm)],[c_4974,c_6895])).

cnf(c_12048,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7062,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,c_60,c_61,c_73,c_6216])).

cnf(c_12049,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12048])).

cnf(c_12056,plain,
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
    inference(superposition,[status(thm)],[c_5710,c_12049])).

cnf(c_63,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_67,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12092,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12056,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67])).

cnf(c_12093,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12092])).

cnf(c_12100,plain,
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
    inference(superposition,[status(thm)],[c_11725,c_12093])).

cnf(c_12304,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12100,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,c_60,c_61,c_63,c_64,c_65,c_67,c_73,c_6216])).

cnf(c_12305,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12304])).

cnf(c_12310,plain,
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
    inference(superposition,[status(thm)],[c_5688,c_12305])).

cnf(c_12456,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12310,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67])).

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
    inference(cnf_transformation,[],[f57])).

cnf(c_1941,plain,
    ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54)
    | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),X1_54,X0_54)
    | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),X2_54,X0_54)
    | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),u1_struct_0(X1_54),u1_struct_0(X0_54))
    | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54))
    | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
    | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
    | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52))
    | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4981,plain,
    ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),X1_54,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),X2_54,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_10178,plain,
    ( sP0(X0_54,sK5,X0_52,sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),sK4,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1929,c_4981])).

cnf(c_10188,plain,
    ( sP0(X0_54,sK5,X0_52,sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),sK5,X0_54) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),sK4,X0_54) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10178,c_1929])).

cnf(c_12461,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12456,c_10188])).

cnf(c_26,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_514,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1,c_26])).

cnf(c_515,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_1(sK6)
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_517,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_35,c_34,c_32])).

cnf(c_518,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_517])).

cnf(c_1907,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
    | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_518])).

cnf(c_4993,plain,
    ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1907])).

cnf(c_5187,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4993,c_1929])).

cnf(c_6614,plain,
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
    inference(superposition,[status(thm)],[c_4973,c_5187])).

cnf(c_6927,plain,
    ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6614,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,c_60,c_61,c_73,c_6216])).

cnf(c_6928,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6927])).

cnf(c_7063,plain,
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
    inference(superposition,[status(thm)],[c_4974,c_6928])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1934,plain,
    ( ~ sP0(X0_54,X1_54,X0_52,X2_54,X3_54)
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_4988,plain,
    ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_7166,plain,
    ( sP0(X0_54,sK5,X0_52,sK4,sK2) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1929,c_4988])).

cnf(c_7218,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7166,c_6928])).

cnf(c_7492,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7218,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,c_60,c_61,c_73,c_6216,c_7063])).

cnf(c_7500,plain,
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
    inference(superposition,[status(thm)],[c_5710,c_7492])).

cnf(c_7607,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7500,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67])).

cnf(c_7608,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7607])).

cnf(c_11746,plain,
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
    inference(superposition,[status(thm)],[c_11725,c_7608])).

cnf(c_12150,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7063,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,c_60,c_61,c_63,c_64,c_65,c_67,c_73,c_6216,c_11746])).

cnf(c_12151,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12150])).

cnf(c_12156,plain,
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
    inference(superposition,[status(thm)],[c_5688,c_12151])).

cnf(c_12167,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12156,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67])).

cnf(c_12578,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12461,c_12167,c_12456])).

cnf(c_33,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_62,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_66,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12596,plain,
    ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12578,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1945,plain,
    ( ~ sP1(X0_54,X1_54,X0_52,X2_54,X3_54)
    | ~ sP0(X3_54,X2_54,X0_52,X1_54,X0_54)
    | v5_pre_topc(X0_52,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4977,plain,
    ( sP1(X0_54,X1_54,X0_52,X2_54,X3_54) != iProver_top
    | sP0(X3_54,X2_54,X0_52,X1_54,X0_54) != iProver_top
    | v5_pre_topc(X0_52,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1945])).

cnf(c_8336,plain,
    ( sP1(sK2,sK4,X0_52,sK5,X0_54) != iProver_top
    | sP0(X0_54,sK5,X0_52,sK4,sK2) != iProver_top
    | v5_pre_topc(X0_52,sK2,X0_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1929,c_4977])).

cnf(c_12602,plain,
    ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_12596,c_8336])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_1932,plain,
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
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_8523,plain,
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
    inference(instantiation,[status(thm)],[c_1932])).

cnf(c_8529,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_8523])).

cnf(c_8531,plain,
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
    inference(instantiation,[status(thm)],[c_8529])).

cnf(c_5596,plain,
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
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_6274,plain,
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
    inference(instantiation,[status(thm)],[c_5596])).

cnf(c_6275,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_6274])).

cnf(c_6277,plain,
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
    inference(instantiation,[status(thm)],[c_6275])).

cnf(c_5595,plain,
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
    inference(instantiation,[status(thm)],[c_1952])).

cnf(c_6246,plain,
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
    inference(instantiation,[status(thm)],[c_5595])).

cnf(c_6247,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_6246])).

cnf(c_6249,plain,
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
    inference(instantiation,[status(thm)],[c_6247])).

cnf(c_24,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1930,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_5014,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1930])).

cnf(c_5725,plain,
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
    inference(superposition,[status(thm)],[c_5710,c_5014])).

cnf(c_5733,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5725,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67])).

cnf(c_5734,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5733])).

cnf(c_5740,plain,
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
    inference(superposition,[status(thm)],[c_5688,c_5734])).

cnf(c_5753,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5740,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67])).

cnf(c_37,negated_conjecture,
    ( v1_borsuk_1(sK5,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_58,plain,
    ( v1_borsuk_1(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,negated_conjecture,
    ( v1_borsuk_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_55,plain,
    ( v1_borsuk_1(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12602,c_8531,c_6277,c_6249,c_6216,c_5753,c_67,c_65,c_64,c_63,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_53,c_52,c_51,c_50,c_49,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:51:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.60/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.60/1.48  
% 7.60/1.48  ------  iProver source info
% 7.60/1.48  
% 7.60/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.60/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.60/1.48  git: non_committed_changes: false
% 7.60/1.48  git: last_make_outside_of_git: false
% 7.60/1.48  
% 7.60/1.48  ------ 
% 7.60/1.48  ------ Parsing...
% 7.60/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  ------ Proving...
% 7.60/1.48  ------ Problem Properties 
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  clauses                                 46
% 7.60/1.48  conjectures                             22
% 7.60/1.48  EPR                                     18
% 7.60/1.48  Horn                                    39
% 7.60/1.48  unary                                   21
% 7.60/1.48  binary                                  9
% 7.60/1.48  lits                                    181
% 7.60/1.48  lits eq                                 3
% 7.60/1.48  fd_pure                                 0
% 7.60/1.48  fd_pseudo                               0
% 7.60/1.48  fd_cond                                 0
% 7.60/1.48  fd_pseudo_cond                          0
% 7.60/1.48  AC symbols                              0
% 7.60/1.48  
% 7.60/1.48  ------ Input Options Time Limit: Unbounded
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing...
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.60/1.48  Current options:
% 7.60/1.48  ------ 
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 34 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing...
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 41 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing...
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 46 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing...
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 46 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  % SZS status Theorem for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  fof(f6,conjecture,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f7,negated_conjecture,(
% 7.60/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 7.60/1.48    inference(negated_conjecture,[],[f6])).
% 7.60/1.48  
% 7.60/1.48  fof(f17,plain,(
% 7.60/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f7])).
% 7.60/1.48  
% 7.60/1.48  fof(f18,plain,(
% 7.60/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f17])).
% 7.60/1.48  
% 7.60/1.48  fof(f34,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),sK7) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK7)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK7,X3,X1) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f33,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK6,X5)),sK6) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK6,X2,X1) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f32,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5))) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),sK5,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK5),X2,k10_tmap_1(X0,X1,X2,sK5,X4,X5)),X4) & k1_tsep_1(X0,X2,sK5) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(X5,sK5,X1) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & v1_borsuk_1(sK5,X0) & ~v2_struct_0(sK5))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f31,plain,(
% 7.60/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),X3,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,X3),sK4,k10_tmap_1(X0,X1,sK4,X3,X4,X5)),X4) & k1_tsep_1(X0,sK4,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(X4,sK4,X1) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & v1_borsuk_1(sK4,X0) & ~v2_struct_0(sK4))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f30,plain,(
% 7.60/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),X0,sK3) | ~v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK3,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f29,plain,(
% 7.60/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),sK2,X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,k10_tmap_1(sK2,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(sK2,X2,X3) = sK2 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_borsuk_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_borsuk_1(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f35,plain,(
% 7.60/1.48    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) & r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) & k1_tsep_1(sK2,sK4,sK5) = sK2 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & v1_borsuk_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & v1_borsuk_1(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.60/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f18,f34,f33,f32,f31,f30,f29])).
% 7.60/1.48  
% 7.60/1.48  fof(f80,plain,(
% 7.60/1.48    k1_tsep_1(sK2,sK4,sK5) = sK2),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f2,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f10,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f2])).
% 7.60/1.48  
% 7.60/1.48  fof(f11,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f10])).
% 7.60/1.48  
% 7.60/1.48  fof(f39,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f11])).
% 7.60/1.48  
% 7.60/1.48  fof(f60,plain,(
% 7.60/1.48    ~v2_struct_0(sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f61,plain,(
% 7.60/1.48    v2_pre_topc(sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f62,plain,(
% 7.60/1.48    l1_pre_topc(sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f66,plain,(
% 7.60/1.48    ~v2_struct_0(sK4)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f68,plain,(
% 7.60/1.48    m1_pre_topc(sK4,sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f69,plain,(
% 7.60/1.48    ~v2_struct_0(sK5)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f71,plain,(
% 7.60/1.48    m1_pre_topc(sK5,sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f40,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f11])).
% 7.60/1.48  
% 7.60/1.48  fof(f3,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f12,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f3])).
% 7.60/1.48  
% 7.60/1.48  fof(f13,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f12])).
% 7.60/1.48  
% 7.60/1.48  fof(f41,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f13])).
% 7.60/1.48  
% 7.60/1.48  fof(f42,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f13])).
% 7.60/1.48  
% 7.60/1.48  fof(f43,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f13])).
% 7.60/1.48  
% 7.60/1.48  fof(f1,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f8,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.60/1.48    inference(ennf_transformation,[],[f1])).
% 7.60/1.48  
% 7.60/1.48  fof(f9,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.60/1.48    inference(flattening,[],[f8])).
% 7.60/1.48  
% 7.60/1.48  fof(f22,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.60/1.48    inference(nnf_transformation,[],[f9])).
% 7.60/1.48  
% 7.60/1.48  fof(f36,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f22])).
% 7.60/1.48  
% 7.60/1.48  fof(f82,plain,(
% 7.60/1.48    r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f76,plain,(
% 7.60/1.48    v1_funct_1(sK7)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f77,plain,(
% 7.60/1.48    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f79,plain,(
% 7.60/1.48    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f63,plain,(
% 7.60/1.48    ~v2_struct_0(sK3)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f64,plain,(
% 7.60/1.48    v2_pre_topc(sK3)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f65,plain,(
% 7.60/1.48    l1_pre_topc(sK3)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f72,plain,(
% 7.60/1.48    v1_funct_1(sK6)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f73,plain,(
% 7.60/1.48    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f5,axiom,(
% 7.60/1.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f16,plain,(
% 7.60/1.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.60/1.48    inference(ennf_transformation,[],[f5])).
% 7.60/1.48  
% 7.60/1.48  fof(f59,plain,(
% 7.60/1.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f16])).
% 7.60/1.48  
% 7.60/1.48  fof(f75,plain,(
% 7.60/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f38,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f11])).
% 7.60/1.48  
% 7.60/1.48  fof(f19,plain,(
% 7.60/1.48    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 7.60/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.60/1.48  
% 7.60/1.48  fof(f26,plain,(
% 7.60/1.48    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 7.60/1.48    inference(nnf_transformation,[],[f19])).
% 7.60/1.48  
% 7.60/1.48  fof(f27,plain,(
% 7.60/1.48    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 7.60/1.48    inference(flattening,[],[f26])).
% 7.60/1.48  
% 7.60/1.48  fof(f28,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 7.60/1.48    inference(rectify,[],[f27])).
% 7.60/1.48  
% 7.60/1.48  fof(f57,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f28])).
% 7.60/1.48  
% 7.60/1.48  fof(f81,plain,(
% 7.60/1.48    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f50,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f28])).
% 7.60/1.48  
% 7.60/1.48  fof(f74,plain,(
% 7.60/1.48    v5_pre_topc(sK6,sK4,sK3)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f78,plain,(
% 7.60/1.48    v5_pre_topc(sK7,sK5,sK3)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f20,plain,(
% 7.60/1.48    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 7.60/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.60/1.48  
% 7.60/1.48  fof(f23,plain,(
% 7.60/1.48    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 7.60/1.48    inference(nnf_transformation,[],[f20])).
% 7.60/1.48  
% 7.60/1.48  fof(f24,plain,(
% 7.60/1.48    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 7.60/1.48    inference(flattening,[],[f23])).
% 7.60/1.48  
% 7.60/1.48  fof(f25,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 7.60/1.48    inference(rectify,[],[f24])).
% 7.60/1.48  
% 7.60/1.48  fof(f47,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f25])).
% 7.60/1.48  
% 7.60/1.48  fof(f4,axiom,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))))))))),
% 7.60/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f14,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f4])).
% 7.60/1.48  
% 7.60/1.48  fof(f15,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f14])).
% 7.60/1.48  
% 7.60/1.48  fof(f21,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(definition_folding,[],[f15,f20,f19])).
% 7.60/1.48  
% 7.60/1.48  fof(f58,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~v1_borsuk_1(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f21])).
% 7.60/1.48  
% 7.60/1.48  fof(f83,plain,(
% 7.60/1.48    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f70,plain,(
% 7.60/1.48    v1_borsuk_1(sK5,sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f67,plain,(
% 7.60/1.48    v1_borsuk_1(sK4,sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  cnf(c_27,negated_conjecture,
% 7.60/1.48      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 7.60/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1929,negated_conjecture,
% 7.60/1.48      ( k1_tsep_1(sK2,sK4,sK5) = sK2 ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_27]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.60/1.48      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X1,X5)
% 7.60/1.48      | ~ m1_pre_topc(X4,X5)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X5)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ l1_pre_topc(X5)
% 7.60/1.48      | v2_struct_0(X5)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X1)
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | ~ v1_funct_1(X3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1951,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.60/1.48      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 7.60/1.48      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))
% 7.60/1.48      | ~ m1_pre_topc(X2_54,X3_54)
% 7.60/1.48      | ~ m1_pre_topc(X0_54,X3_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ v2_pre_topc(X3_54)
% 7.60/1.48      | ~ v2_pre_topc(X1_54)
% 7.60/1.48      | ~ l1_pre_topc(X3_54)
% 7.60/1.48      | ~ l1_pre_topc(X1_54)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(X3_54)
% 7.60/1.48      | v2_struct_0(X2_54)
% 7.60/1.48      | ~ v1_funct_1(X0_52)
% 7.60/1.48      | ~ v1_funct_1(X1_52) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4971,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)) = iProver_top
% 7.60/1.48      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1951]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5591,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1929,c_4971]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_47,negated_conjecture,
% 7.60/1.48      ( ~ v2_struct_0(sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_48,plain,
% 7.60/1.48      ( v2_struct_0(sK2) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_46,negated_conjecture,
% 7.60/1.48      ( v2_pre_topc(sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_49,plain,
% 7.60/1.48      ( v2_pre_topc(sK2) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_45,negated_conjecture,
% 7.60/1.48      ( l1_pre_topc(sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_50,plain,
% 7.60/1.48      ( l1_pre_topc(sK2) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_41,negated_conjecture,
% 7.60/1.48      ( ~ v2_struct_0(sK4) ),
% 7.60/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_54,plain,
% 7.60/1.48      ( v2_struct_0(sK4) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_39,negated_conjecture,
% 7.60/1.48      ( m1_pre_topc(sK4,sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_56,plain,
% 7.60/1.48      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_38,negated_conjecture,
% 7.60/1.48      ( ~ v2_struct_0(sK5) ),
% 7.60/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_57,plain,
% 7.60/1.48      ( v2_struct_0(sK5) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_36,negated_conjecture,
% 7.60/1.48      ( m1_pre_topc(sK5,sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_59,plain,
% 7.60/1.48      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5687,plain,
% 7.60/1.48      ( v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_5591,c_48,c_49,c_50,c_54,c_56,c_57,c_59]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5688,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) = iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_5687]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X1,X5)
% 7.60/1.48      | ~ m1_pre_topc(X4,X5)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.60/1.48      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X5)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ l1_pre_topc(X5)
% 7.60/1.48      | v2_struct_0(X5)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X1)
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | ~ v1_funct_1(X3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1952,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.60/1.48      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 7.60/1.48      | ~ m1_pre_topc(X2_54,X3_54)
% 7.60/1.48      | ~ m1_pre_topc(X0_54,X3_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.60/1.48      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ v2_pre_topc(X3_54)
% 7.60/1.48      | ~ v2_pre_topc(X1_54)
% 7.60/1.48      | ~ l1_pre_topc(X3_54)
% 7.60/1.48      | ~ l1_pre_topc(X1_54)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(X3_54)
% 7.60/1.48      | v2_struct_0(X2_54)
% 7.60/1.48      | ~ v1_funct_1(X0_52)
% 7.60/1.48      | ~ v1_funct_1(X1_52) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4970,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X2_54,X0_54)),u1_struct_0(X1_54)))) = iProver_top
% 7.60/1.48      | v2_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1952]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5480,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1929,c_4970]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5709,plain,
% 7.60/1.48      ( v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_5480,c_48,c_49,c_50,c_54,c_56,c_57,c_59]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5710,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) = iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_5709]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X3,X4)
% 7.60/1.48      | ~ m1_pre_topc(X1,X4)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X4)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ l1_pre_topc(X4)
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1947,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.60/1.48      | ~ m1_pre_topc(X2_54,X3_54)
% 7.60/1.48      | ~ m1_pre_topc(X0_54,X3_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ v2_pre_topc(X3_54)
% 7.60/1.48      | ~ v2_pre_topc(X1_54)
% 7.60/1.48      | ~ l1_pre_topc(X3_54)
% 7.60/1.48      | ~ l1_pre_topc(X1_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(X3_54)
% 7.60/1.48      | ~ v1_funct_1(X0_52)
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4975,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1947]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7800,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52),u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,X2_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X2_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X2_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5710,c_4975]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_11724,plain,
% 7.60/1.48      ( v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,X2_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X2_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X2_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7800,c_48,c_49,c_50,c_54,c_56,c_57,c_59,c_5591]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_11725,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,X2_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X2_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X2_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X2_54,X0_54,sK2,X1_54,k10_tmap_1(sK2,X0_54,sK4,sK5,X1_52,X0_52))) = iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_11724]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X4,X3)
% 7.60/1.48      | ~ m1_pre_topc(X1,X3)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X3)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ l1_pre_topc(X3)
% 7.60/1.48      | v2_struct_0(X3)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | ~ v1_funct_1(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1948,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54))
% 7.60/1.48      | ~ m1_pre_topc(X3_54,X2_54)
% 7.60/1.48      | ~ m1_pre_topc(X0_54,X2_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ v2_pre_topc(X2_54)
% 7.60/1.48      | ~ v2_pre_topc(X1_54)
% 7.60/1.48      | ~ l1_pre_topc(X2_54)
% 7.60/1.48      | ~ l1_pre_topc(X1_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(X2_54)
% 7.60/1.48      | ~ v1_funct_1(X0_52) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4974,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X2_54,X1_54,X0_54,X3_54,X0_52),u1_struct_0(X3_54),u1_struct_0(X1_54)) = iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X2_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X2_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1948]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X3,X4)
% 7.60/1.48      | ~ m1_pre_topc(X1,X4)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X4)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ l1_pre_topc(X4)
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | ~ v1_funct_1(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1949,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.60/1.48      | ~ m1_pre_topc(X2_54,X3_54)
% 7.60/1.48      | ~ m1_pre_topc(X0_54,X3_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.60/1.48      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ v2_pre_topc(X3_54)
% 7.60/1.48      | ~ v2_pre_topc(X1_54)
% 7.60/1.48      | ~ l1_pre_topc(X3_54)
% 7.60/1.48      | ~ l1_pre_topc(X1_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(X3_54)
% 7.60/1.48      | ~ v1_funct_1(X0_52) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4973,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 7.60/1.48      | v2_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1,plain,
% 7.60/1.48      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.60/1.48      | ~ v1_funct_2(X3,X0,X1)
% 7.60/1.48      | ~ v1_funct_2(X2,X0,X1)
% 7.60/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.60/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.60/1.48      | ~ v1_funct_1(X3)
% 7.60/1.48      | ~ v1_funct_1(X2)
% 7.60/1.48      | X2 = X3 ),
% 7.60/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_25,negated_conjecture,
% 7.60/1.48      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) ),
% 7.60/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_494,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.60/1.48      | ~ v1_funct_2(X3,X1,X2)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | ~ v1_funct_1(X3)
% 7.60/1.48      | X3 = X0
% 7.60/1.48      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 7.60/1.48      | u1_struct_0(sK5) != X1
% 7.60/1.48      | u1_struct_0(sK3) != X2
% 7.60/1.48      | sK7 != X3 ),
% 7.60/1.48      inference(resolution_lifted,[status(thm)],[c_1,c_25]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_495,plain,
% 7.60/1.48      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.60/1.48      | ~ v1_funct_1(sK7)
% 7.60/1.48      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(unflattening,[status(thm)],[c_494]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_31,negated_conjecture,
% 7.60/1.48      ( v1_funct_1(sK7) ),
% 7.60/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_30,negated_conjecture,
% 7.60/1.48      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_28,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 7.60/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_497,plain,
% 7.60/1.48      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.60/1.48      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_495,c_31,c_30,c_28]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_498,plain,
% 7.60/1.48      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.60/1.48      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_497]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1908,plain,
% 7.60/1.48      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.60/1.48      | sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_498]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4992,plain,
% 7.60/1.48      ( sK7 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1908]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5178,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(light_normalisation,[status(thm)],[c_4992,c_1929]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6613,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_4973,c_5178]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_44,negated_conjecture,
% 7.60/1.48      ( ~ v2_struct_0(sK3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_51,plain,
% 7.60/1.48      ( v2_struct_0(sK3) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_43,negated_conjecture,
% 7.60/1.48      ( v2_pre_topc(sK3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_52,plain,
% 7.60/1.48      ( v2_pre_topc(sK3) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_42,negated_conjecture,
% 7.60/1.48      ( l1_pre_topc(sK3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_53,plain,
% 7.60/1.48      ( l1_pre_topc(sK3) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_35,negated_conjecture,
% 7.60/1.48      ( v1_funct_1(sK6) ),
% 7.60/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_60,plain,
% 7.60/1.48      ( v1_funct_1(sK6) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_34,negated_conjecture,
% 7.60/1.48      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_61,plain,
% 7.60/1.48      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_23,plain,
% 7.60/1.48      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_71,plain,
% 7.60/1.48      ( m1_pre_topc(X0,X0) = iProver_top
% 7.60/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_73,plain,
% 7.60/1.48      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_71]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_32,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 7.60/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1924,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_32]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5009,plain,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1928,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_28]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5013,plain,
% 7.60/1.48      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1928]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X1,X5)
% 7.60/1.48      | ~ m1_pre_topc(X4,X5)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X5)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ l1_pre_topc(X5)
% 7.60/1.48      | v2_struct_0(X5)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X1)
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | ~ v1_funct_1(X3)
% 7.60/1.48      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f38]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1950,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 7.60/1.48      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 7.60/1.48      | ~ m1_pre_topc(X2_54,X3_54)
% 7.60/1.48      | ~ m1_pre_topc(X0_54,X3_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 7.60/1.48      | ~ v2_pre_topc(X3_54)
% 7.60/1.48      | ~ v2_pre_topc(X1_54)
% 7.60/1.48      | ~ l1_pre_topc(X3_54)
% 7.60/1.48      | ~ l1_pre_topc(X1_54)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(X3_54)
% 7.60/1.48      | v2_struct_0(X2_54)
% 7.60/1.48      | ~ v1_funct_1(X0_52)
% 7.60/1.48      | ~ v1_funct_1(X1_52)
% 7.60/1.48      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52)) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4972,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_52) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X2_54,X0_54,X1_52,X0_52)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1950]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5804,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,X1_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5013,c_4972]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_64,plain,
% 7.60/1.48      ( v1_funct_1(sK7) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_65,plain,
% 7.60/1.48      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6072,plain,
% 7.60/1.48      ( v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,X1_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.60/1.48      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_5804,c_51,c_52,c_53,c_57,c_64,c_65]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6073,plain,
% 7.60/1.48      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,X1_54) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.60/1.48      | v1_funct_1(X0_52) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7)) = iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_6072]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6089,plain,
% 7.60/1.48      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,X0_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5009,c_6073]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6216,plain,
% 7.60/1.48      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_6089]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6894,plain,
% 7.60/1.48      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_6613,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,
% 7.60/1.48                 c_60,c_61,c_73,c_6216]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6895,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_6894]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7062,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_4974,c_6895]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12048,plain,
% 7.60/1.48      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7062,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,
% 7.60/1.48                 c_60,c_61,c_73,c_6216]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12049,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_12048]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12056,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5710,c_12049]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_63,plain,
% 7.60/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_67,plain,
% 7.60/1.48      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12092,plain,
% 7.60/1.48      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_12056,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12093,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_12092]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12100,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_11725,c_12093]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12304,plain,
% 7.60/1.48      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_12100,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,
% 7.60/1.48                 c_60,c_61,c_63,c_64,c_65,c_67,c_73,c_6216]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12305,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_12304]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12310,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5688,c_12305]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12456,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_12310,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_13,plain,
% 7.60/1.48      ( sP0(X0,X1,X2,X3,X4)
% 7.60/1.48      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 7.60/1.48      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 7.60/1.48      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 7.60/1.48      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1941,plain,
% 7.60/1.48      ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54)
% 7.60/1.48      | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),X1_54,X0_54)
% 7.60/1.48      | ~ v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),X2_54,X0_54)
% 7.60/1.48      | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),u1_struct_0(X1_54),u1_struct_0(X0_54))
% 7.60/1.48      | ~ v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54))))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54))))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52)) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_13]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4981,plain,
% 7.60/1.48      ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54) = iProver_top
% 7.60/1.48      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),X1_54,X0_54) != iProver_top
% 7.60/1.48      | v5_pre_topc(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),X2_54,X0_54) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X1_54,X0_52)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52)) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1941]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10178,plain,
% 7.60/1.48      ( sP0(X0_54,sK5,X0_52,sK4,sK2) = iProver_top
% 7.60/1.48      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),sK5,X0_54) != iProver_top
% 7.60/1.48      | v5_pre_topc(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),sK4,X0_54) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK5,X0_52)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,X0_54,k1_tsep_1(sK2,sK4,sK5),sK4,X0_52)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1929,c_4981]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10188,plain,
% 7.60/1.48      ( sP0(X0_54,sK5,X0_52,sK4,sK2) = iProver_top
% 7.60/1.48      | v5_pre_topc(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),sK5,X0_54) != iProver_top
% 7.60/1.48      | v5_pre_topc(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),sK4,X0_54) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),u1_struct_0(sK5),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,X0_54,sK2,sK5,X0_52)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52)) != iProver_top ),
% 7.60/1.48      inference(light_normalisation,[status(thm)],[c_10178,c_1929]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12461,plain,
% 7.60/1.48      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 7.60/1.48      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
% 7.60/1.48      | v5_pre_topc(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_12456,c_10188]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_26,negated_conjecture,
% 7.60/1.48      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) ),
% 7.60/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_514,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.60/1.48      | ~ v1_funct_2(X3,X1,X2)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | ~ v1_funct_1(X3)
% 7.60/1.48      | X3 = X0
% 7.60/1.48      | k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != X0
% 7.60/1.48      | u1_struct_0(sK4) != X1
% 7.60/1.48      | u1_struct_0(sK3) != X2
% 7.60/1.48      | sK6 != X3 ),
% 7.60/1.48      inference(resolution_lifted,[status(thm)],[c_1,c_26]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_515,plain,
% 7.60/1.48      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 7.60/1.48      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.60/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.60/1.48      | ~ v1_funct_1(sK6)
% 7.60/1.48      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(unflattening,[status(thm)],[c_514]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_517,plain,
% 7.60/1.48      ( ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.60/1.48      | ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.60/1.48      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_515,c_35,c_34,c_32]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_518,plain,
% 7.60/1.48      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.60/1.48      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_517]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1907,plain,
% 7.60/1.48      ( ~ v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)))
% 7.60/1.48      | sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_518]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4993,plain,
% 7.60/1.48      ( sK6 = k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1907]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5187,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(light_normalisation,[status(thm)],[c_4993,c_1929]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6614,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_4973,c_5187]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6927,plain,
% 7.60/1.48      ( m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_6614,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,
% 7.60/1.48                 c_60,c_61,c_73,c_6216]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6928,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_6927]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7063,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_4974,c_6928]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_20,plain,
% 7.60/1.48      ( ~ sP0(X0,X1,X2,X3,X4)
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1934,plain,
% 7.60/1.48      ( ~ sP0(X0_54,X1_54,X0_52,X2_54,X3_54)
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54)) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_20]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4988,plain,
% 7.60/1.48      ( sP0(X0_54,X1_54,X0_52,X2_54,X3_54) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X3_54,X0_54,k1_tsep_1(X3_54,X2_54,X1_54),X2_54,X0_52),u1_struct_0(X2_54),u1_struct_0(X0_54)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7166,plain,
% 7.60/1.48      ( sP0(X0_54,sK5,X0_52,sK4,sK2) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(sK2,X0_54,sK2,sK4,X0_52),u1_struct_0(sK4),u1_struct_0(X0_54)) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1929,c_4988]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7218,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_7166,c_6928]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7492,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7218,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,
% 7.60/1.48                 c_60,c_61,c_73,c_6216,c_7063]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7500,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5710,c_7492]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7607,plain,
% 7.60/1.48      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7500,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7608,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_7607]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_11746,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_11725,c_7608]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12150,plain,
% 7.60/1.48      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7063,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_56,c_59,
% 7.60/1.48                 c_60,c_61,c_63,c_64,c_65,c_67,c_73,c_6216,c_11746]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12151,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_12150]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12156,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5688,c_12151]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12167,plain,
% 7.60/1.48      ( k3_tmap_1(sK2,sK3,sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_12156,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12578,plain,
% 7.60/1.48      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top
% 7.60/1.48      | v5_pre_topc(sK7,sK5,sK3) != iProver_top
% 7.60/1.48      | v5_pre_topc(sK6,sK4,sK3) != iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(light_normalisation,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_12461,c_12167,c_12456]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_33,negated_conjecture,
% 7.60/1.48      ( v5_pre_topc(sK6,sK4,sK3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_62,plain,
% 7.60/1.48      ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_29,negated_conjecture,
% 7.60/1.48      ( v5_pre_topc(sK7,sK5,sK3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_66,plain,
% 7.60/1.48      ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12596,plain,
% 7.60/1.48      ( sP0(sK3,sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4,sK2) = iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_12578,c_60,c_61,c_62,c_63,c_64,c_65,c_66,c_67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_9,plain,
% 7.60/1.48      ( ~ sP1(X0,X1,X2,X3,X4)
% 7.60/1.48      | ~ sP0(X4,X3,X2,X1,X0)
% 7.60/1.48      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 7.60/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1945,plain,
% 7.60/1.48      ( ~ sP1(X0_54,X1_54,X0_52,X2_54,X3_54)
% 7.60/1.48      | ~ sP0(X3_54,X2_54,X0_52,X1_54,X0_54)
% 7.60/1.48      | v5_pre_topc(X0_52,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4977,plain,
% 7.60/1.48      ( sP1(X0_54,X1_54,X0_52,X2_54,X3_54) != iProver_top
% 7.60/1.48      | sP0(X3_54,X2_54,X0_52,X1_54,X0_54) != iProver_top
% 7.60/1.48      | v5_pre_topc(X0_52,k1_tsep_1(X0_54,X1_54,X2_54),X3_54) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1945]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8336,plain,
% 7.60/1.48      ( sP1(sK2,sK4,X0_52,sK5,X0_54) != iProver_top
% 7.60/1.48      | sP0(X0_54,sK5,X0_52,sK4,sK2) != iProver_top
% 7.60/1.48      | v5_pre_topc(X0_52,sK2,X0_54) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1929,c_4977]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12602,plain,
% 7.60/1.48      ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) != iProver_top
% 7.60/1.48      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_12596,c_8336]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_22,plain,
% 7.60/1.48      ( sP1(X0,X1,X2,X3,X4)
% 7.60/1.48      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 7.60/1.48      | ~ v1_borsuk_1(X3,X0)
% 7.60/1.48      | ~ v1_borsuk_1(X1,X0)
% 7.60/1.48      | ~ m1_pre_topc(X3,X0)
% 7.60/1.48      | ~ m1_pre_topc(X1,X0)
% 7.60/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 7.60/1.48      | ~ v2_pre_topc(X4)
% 7.60/1.48      | ~ v2_pre_topc(X0)
% 7.60/1.48      | ~ l1_pre_topc(X4)
% 7.60/1.48      | ~ l1_pre_topc(X0)
% 7.60/1.48      | v2_struct_0(X0)
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X1)
% 7.60/1.48      | v2_struct_0(X3)
% 7.60/1.48      | ~ v1_funct_1(X2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1932,plain,
% 7.60/1.48      ( sP1(X0_54,X1_54,X0_52,X2_54,X3_54)
% 7.60/1.48      | ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))
% 7.60/1.48      | ~ v1_borsuk_1(X1_54,X0_54)
% 7.60/1.48      | ~ v1_borsuk_1(X2_54,X0_54)
% 7.60/1.48      | ~ m1_pre_topc(X1_54,X0_54)
% 7.60/1.48      | ~ m1_pre_topc(X2_54,X0_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))))
% 7.60/1.48      | ~ v2_pre_topc(X0_54)
% 7.60/1.48      | ~ v2_pre_topc(X3_54)
% 7.60/1.48      | ~ l1_pre_topc(X0_54)
% 7.60/1.48      | ~ l1_pre_topc(X3_54)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(X3_54)
% 7.60/1.48      | v2_struct_0(X2_54)
% 7.60/1.48      | ~ v1_funct_1(X0_52) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_22]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8523,plain,
% 7.60/1.48      ( sP1(X0_54,sK4,k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5,sK3)
% 7.60/1.48      | ~ v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))
% 7.60/1.48      | ~ v1_borsuk_1(sK5,X0_54)
% 7.60/1.48      | ~ v1_borsuk_1(sK4,X0_54)
% 7.60/1.48      | ~ m1_pre_topc(sK5,X0_54)
% 7.60/1.48      | ~ m1_pre_topc(sK4,X0_54)
% 7.60/1.48      | ~ m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v2_pre_topc(X0_54)
% 7.60/1.48      | ~ v2_pre_topc(sK3)
% 7.60/1.48      | ~ l1_pre_topc(X0_54)
% 7.60/1.48      | ~ l1_pre_topc(sK3)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(sK5)
% 7.60/1.48      | v2_struct_0(sK4)
% 7.60/1.48      | v2_struct_0(sK3)
% 7.60/1.48      | ~ v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1932]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8529,plain,
% 7.60/1.48      ( sP1(X0_54,sK4,k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_borsuk_1(sK5,X0_54) != iProver_top
% 7.60/1.48      | v1_borsuk_1(sK4,X0_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,X0_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,X0_54) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_8523]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8531,plain,
% 7.60/1.48      ( sP1(sK2,sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5,sK3) = iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_borsuk_1(sK5,sK2) != iProver_top
% 7.60/1.48      | v1_borsuk_1(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_8529]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5596,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3))
% 7.60/1.48      | v1_funct_2(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7),u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))
% 7.60/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_pre_topc(X0_54,X1_54)
% 7.60/1.48      | ~ m1_pre_topc(sK5,X1_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 7.60/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v2_pre_topc(X1_54)
% 7.60/1.48      | ~ v2_pre_topc(sK3)
% 7.60/1.48      | ~ l1_pre_topc(X1_54)
% 7.60/1.48      | ~ l1_pre_topc(sK3)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(sK5)
% 7.60/1.48      | v2_struct_0(sK3)
% 7.60/1.48      | ~ v1_funct_1(X0_52)
% 7.60/1.48      | ~ v1_funct_1(sK7) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1951]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6274,plain,
% 7.60/1.48      ( v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))
% 7.60/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_pre_topc(sK5,X0_54)
% 7.60/1.48      | ~ m1_pre_topc(sK4,X0_54)
% 7.60/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v2_pre_topc(X0_54)
% 7.60/1.48      | ~ v2_pre_topc(sK3)
% 7.60/1.48      | ~ l1_pre_topc(X0_54)
% 7.60/1.48      | ~ l1_pre_topc(sK3)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(sK5)
% 7.60/1.48      | v2_struct_0(sK4)
% 7.60/1.48      | v2_struct_0(sK3)
% 7.60/1.48      | ~ v1_funct_1(sK7)
% 7.60/1.48      | ~ v1_funct_1(sK6) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_5596]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6275,plain,
% 7.60/1.48      ( v1_funct_2(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,X0_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,X0_54) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_6274]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6277,plain,
% 7.60/1.48      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_6275]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5595,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK3))
% 7.60/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_pre_topc(X0_54,X1_54)
% 7.60/1.48      | ~ m1_pre_topc(sK5,X1_54)
% 7.60/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK3))))
% 7.60/1.48      | m1_subset_1(k10_tmap_1(X1_54,sK3,X0_54,sK5,X0_52,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_54,X0_54,sK5)),u1_struct_0(sK3))))
% 7.60/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v2_pre_topc(X1_54)
% 7.60/1.48      | ~ v2_pre_topc(sK3)
% 7.60/1.48      | ~ l1_pre_topc(X1_54)
% 7.60/1.48      | ~ l1_pre_topc(sK3)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(X1_54)
% 7.60/1.48      | v2_struct_0(sK5)
% 7.60/1.48      | v2_struct_0(sK3)
% 7.60/1.48      | ~ v1_funct_1(X0_52)
% 7.60/1.48      | ~ v1_funct_1(sK7) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1952]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6246,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 7.60/1.48      | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_pre_topc(sK5,X0_54)
% 7.60/1.48      | ~ m1_pre_topc(sK4,X0_54)
% 7.60/1.48      | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3))))
% 7.60/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 7.60/1.48      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v2_pre_topc(X0_54)
% 7.60/1.48      | ~ v2_pre_topc(sK3)
% 7.60/1.48      | ~ l1_pre_topc(X0_54)
% 7.60/1.48      | ~ l1_pre_topc(sK3)
% 7.60/1.48      | v2_struct_0(X0_54)
% 7.60/1.48      | v2_struct_0(sK5)
% 7.60/1.48      | v2_struct_0(sK4)
% 7.60/1.48      | v2_struct_0(sK3)
% 7.60/1.48      | ~ v1_funct_1(sK7)
% 7.60/1.48      | ~ v1_funct_1(sK6) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_5595]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6247,plain,
% 7.60/1.48      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,X0_54) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,X0_54) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(X0_54,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_6246]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6249,plain,
% 7.60/1.48      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK2) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.60/1.48      | v2_struct_0(sK5) = iProver_top
% 7.60/1.48      | v2_struct_0(sK4) = iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_6247]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_24,negated_conjecture,
% 7.60/1.48      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 7.60/1.48      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1930,negated_conjecture,
% 7.60/1.48      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3)
% 7.60/1.48      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3))
% 7.60/1.48      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 7.60/1.48      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_24]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5014,plain,
% 7.60/1.48      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_1930]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5725,plain,
% 7.60/1.48      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5710,c_5014]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5733,plain,
% 7.60/1.48      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_5725,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5734,plain,
% 7.60/1.48      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.60/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_5733]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5740,plain,
% 7.60/1.48      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.60/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 7.60/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 7.60/1.48      | v1_funct_1(sK7) != iProver_top
% 7.60/1.48      | v1_funct_1(sK6) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_5688,c_5734]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5753,plain,
% 7.60/1.48      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK2,sK3) != iProver_top
% 7.60/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_5740,c_51,c_52,c_53,c_60,c_61,c_63,c_64,c_65,c_67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_37,negated_conjecture,
% 7.60/1.48      ( v1_borsuk_1(sK5,sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_58,plain,
% 7.60/1.48      ( v1_borsuk_1(sK5,sK2) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_40,negated_conjecture,
% 7.60/1.48      ( v1_borsuk_1(sK4,sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_55,plain,
% 7.60/1.48      ( v1_borsuk_1(sK4,sK2) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(contradiction,plain,
% 7.60/1.48      ( $false ),
% 7.60/1.48      inference(minisat,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_12602,c_8531,c_6277,c_6249,c_6216,c_5753,c_67,c_65,
% 7.60/1.48                 c_64,c_63,c_61,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_53,
% 7.60/1.48                 c_52,c_51,c_50,c_49,c_48]) ).
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  ------                               Statistics
% 7.60/1.48  
% 7.60/1.48  ------ Selected
% 7.60/1.48  
% 7.60/1.48  total_time:                             0.514
% 7.60/1.48  
%------------------------------------------------------------------------------

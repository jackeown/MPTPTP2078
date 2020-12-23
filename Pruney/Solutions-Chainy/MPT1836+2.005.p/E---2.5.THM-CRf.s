%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 774 expanded)
%              Number of clauses        :   55 ( 225 expanded)
%              Number of leaves         :    6 ( 187 expanded)
%              Depth                    :   11
%              Number of atoms          :  745 (15608 expanded)
%              Number of equality atoms :    4 ( 534 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal clause size      :   88 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_borsuk_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_borsuk_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & v5_pre_topc(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(X6,X4,X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                         => ( ( X1 = k1_tsep_1(X1,X3,X4)
                              & r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5)
                              & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6) )
                           => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                              & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(X1),u1_struct_0(X2))
                              & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),X1,X2)
                              & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_tmap_1)).

fof(dt_k10_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1)
        & ~ v2_struct_0(X4)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
        & v1_funct_1(X6)
        & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
     => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
        & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(t145_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( r1_tsep_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & v5_pre_topc(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( r4_tsep_1(X1,X3,X4)
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_tmap_1)).

fof(t140_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ~ r1_tsep_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5)
                                & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_tmap_1)).

fof(t87_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_borsuk_1(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_borsuk_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => r4_tsep_1(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).

fof(t144_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ~ r1_tsep_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & v5_pre_topc(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))
                                & r4_tsep_1(X1,X3,X4) )
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_tmap_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v1_borsuk_1(X3,X1)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_borsuk_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & v5_pre_topc(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( ( X1 = k1_tsep_1(X1,X3,X4)
                                & r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5)
                                & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6) )
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(X1),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),X1,X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t152_tmap_1])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( v1_funct_1(k10_tmap_1(X7,X8,X9,X10,X11,X12))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X7)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X7)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8)))) )
      & ( v1_funct_2(k10_tmap_1(X7,X8,X9,X10,X11,X12),u1_struct_0(k1_tsep_1(X7,X9,X10)),u1_struct_0(X8))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X7)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X7)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8)))) )
      & ( m1_subset_1(k10_tmap_1(X7,X8,X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X9,X10)),u1_struct_0(X8))))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X7)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X7)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v1_borsuk_1(esk3_0,esk1_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & v1_borsuk_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & esk1_0 = k1_tsep_1(esk1_0,esk3_0,esk4_0)
    & r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0)
    & r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0)
    & ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
      | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)
      | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_9,plain,
    ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_23,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( v1_funct_1(k10_tmap_1(X25,X26,X27,X28,X29,X30))
        | ~ r4_tsep_1(X25,X27,X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X26))
        | ~ v5_pre_topc(X30,X28,X26)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ v5_pre_topc(X29,X27,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | ~ r1_tsep_1(X27,X28)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_2(k10_tmap_1(X25,X26,X27,X28,X29,X30),u1_struct_0(k1_tsep_1(X25,X27,X28)),u1_struct_0(X26))
        | ~ r4_tsep_1(X25,X27,X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X26))
        | ~ v5_pre_topc(X30,X28,X26)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ v5_pre_topc(X29,X27,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | ~ r1_tsep_1(X27,X28)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v5_pre_topc(k10_tmap_1(X25,X26,X27,X28,X29,X30),k1_tsep_1(X25,X27,X28),X26)
        | ~ r4_tsep_1(X25,X27,X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X26))
        | ~ v5_pre_topc(X30,X28,X26)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ v5_pre_topc(X29,X27,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | ~ r1_tsep_1(X27,X28)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(k10_tmap_1(X25,X26,X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X27,X28)),u1_struct_0(X26))))
        | ~ r4_tsep_1(X25,X27,X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X26))
        | ~ v5_pre_topc(X30,X28,X26)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ v5_pre_topc(X29,X27,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
        | ~ r1_tsep_1(X27,X28)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).

fof(c_0_24,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_funct_2(u1_struct_0(X15),u1_struct_0(X14),k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X15,k10_tmap_1(X13,X14,X15,X16,X17,X18)),X17)
        | ~ r2_funct_2(u1_struct_0(X16),u1_struct_0(X14),k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X16,k10_tmap_1(X13,X14,X15,X16,X17,X18)),X18)
        | r2_funct_2(u1_struct_0(k2_tsep_1(X13,X15,X16)),u1_struct_0(X14),k3_tmap_1(X13,X14,X15,k2_tsep_1(X13,X15,X16),X17),k3_tmap_1(X13,X14,X16,k2_tsep_1(X13,X15,X16),X18))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14))))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
        | r1_tsep_1(X15,X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_funct_2(u1_struct_0(X15),u1_struct_0(X14),k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X15,k10_tmap_1(X13,X14,X15,X16,X17,X18)),X17)
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X13,X15,X16)),u1_struct_0(X14),k3_tmap_1(X13,X14,X15,k2_tsep_1(X13,X15,X16),X17),k3_tmap_1(X13,X14,X16,k2_tsep_1(X13,X15,X16),X18))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14))))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
        | r1_tsep_1(X15,X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_funct_2(u1_struct_0(X16),u1_struct_0(X14),k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X16,k10_tmap_1(X13,X14,X15,X16,X17,X18)),X18)
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X13,X15,X16)),u1_struct_0(X14),k3_tmap_1(X13,X14,X15,k2_tsep_1(X13,X15,X16),X17),k3_tmap_1(X13,X14,X16,k2_tsep_1(X13,X15,X16),X18))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14))))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
        | r1_tsep_1(X15,X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t140_tmap_1])])])])])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_32,plain,
    ( m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,plain,
    ( v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ r1_tsep_1(X3,X4)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X3,X1,X4)),u1_struct_0(X2),k3_tmap_1(X3,X2,X1,k2_tsep_1(X3,X1,X4),X5),k3_tmap_1(X3,X2,X4,k2_tsep_1(X3,X1,X4),X6))
    | r1_tsep_1(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,k10_tmap_1(X3,X2,X1,X4,X5,X6)),X5)
    | ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X4,k10_tmap_1(X3,X2,X1,X4,X5,X6)),X6)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_39,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ v1_borsuk_1(X32,X31)
      | ~ m1_pre_topc(X32,X31)
      | ~ v1_borsuk_1(X33,X31)
      | ~ m1_pre_topc(X33,X31)
      | r4_tsep_1(X31,X32,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t87_tsep_1])])])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_tsep_1(X1,X2,esk4_0),esk2_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r4_tsep_1(X1,X2,esk4_0)
    | ~ v5_pre_topc(X3,X2,esk2_0)
    | ~ r1_tsep_1(X2,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_10]),c_0_34]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),X2),k3_tmap_1(esk1_0,X1,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),X3))
    | r1_tsep_1(esk3_0,esk4_0)
    | v2_struct_0(X1)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,k10_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3)),X3)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,k10_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3)),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X3,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_15]),c_0_30]),c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_36])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r4_tsep_1(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_borsuk_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_borsuk_1(X3,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( v1_borsuk_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_51,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_26]),c_0_36]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

fof(c_0_54,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k10_tmap_1(X19,X20,X21,X22,X23,X24))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X19,X21,X22)),u1_struct_0(X20),k3_tmap_1(X19,X20,X21,k2_tsep_1(X19,X21,X22),X23),k3_tmap_1(X19,X20,X22,k2_tsep_1(X19,X21,X22),X24))
        | ~ r4_tsep_1(X19,X21,X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ v5_pre_topc(X24,X22,X20)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ v5_pre_topc(X23,X21,X20)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | r1_tsep_1(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v1_funct_2(k10_tmap_1(X19,X20,X21,X22,X23,X24),u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X19,X21,X22)),u1_struct_0(X20),k3_tmap_1(X19,X20,X21,k2_tsep_1(X19,X21,X22),X23),k3_tmap_1(X19,X20,X22,k2_tsep_1(X19,X21,X22),X24))
        | ~ r4_tsep_1(X19,X21,X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ v5_pre_topc(X24,X22,X20)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ v5_pre_topc(X23,X21,X20)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | r1_tsep_1(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v5_pre_topc(k10_tmap_1(X19,X20,X21,X22,X23,X24),k1_tsep_1(X19,X21,X22),X20)
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X19,X21,X22)),u1_struct_0(X20),k3_tmap_1(X19,X20,X21,k2_tsep_1(X19,X21,X22),X23),k3_tmap_1(X19,X20,X22,k2_tsep_1(X19,X21,X22),X24))
        | ~ r4_tsep_1(X19,X21,X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ v5_pre_topc(X24,X22,X20)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ v5_pre_topc(X23,X21,X20)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | r1_tsep_1(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(k10_tmap_1(X19,X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X19,X21,X22)),u1_struct_0(X20),k3_tmap_1(X19,X20,X21,k2_tsep_1(X19,X21,X22),X23),k3_tmap_1(X19,X20,X22,k2_tsep_1(X19,X21,X22),X24))
        | ~ r4_tsep_1(X19,X21,X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ v5_pre_topc(X24,X22,X20)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ v5_pre_topc(X23,X21,X20)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | r1_tsep_1(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_tmap_1])])])])])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(X1,esk3_0,esk4_0),esk2_0)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(X1,esk3_0,esk4_0)
    | ~ r1_tsep_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_18]),c_0_45]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_10]),c_0_18]),c_0_11]),c_0_19]),c_0_12]),c_0_20]),c_0_13]),c_0_14])]),c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( r4_tsep_1(esk1_0,X1,esk4_0)
    | ~ v1_borsuk_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_26]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( v1_borsuk_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_26]),c_0_36]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_61,plain,
    ( v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(X1,esk3_0,esk4_0),esk2_0)
    | r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))
    | v2_struct_0(X1)
    | ~ r4_tsep_1(X1,esk3_0,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r4_tsep_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_27])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_65,plain,
    ( v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v5_pre_topc(X6,X4,X2)
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_61,c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_36]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_64]),c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_36]),c_0_63]),c_0_34]),c_0_45]),c_0_10]),c_0_18]),c_0_11]),c_0_19]),c_0_12]),c_0_20]),c_0_26]),c_0_27]),c_0_13]),c_0_28]),c_0_14]),c_0_29])]),c_0_64]),c_0_15]),c_0_21]),c_0_16]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S059A
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.030 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t152_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v1_borsuk_1(X3,X1))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_borsuk_1(X4,X1))&m1_pre_topc(X4,X1))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(((X1=k1_tsep_1(X1,X3,X4)&r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5))&r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),X1,X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_tmap_1)).
% 0.20/0.42  fof(dt_k10_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(X6))&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 0.20/0.42  fof(t145_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r1_tsep_1(X3,X4)=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(r4_tsep_1(X1,X3,X4)=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_tmap_1)).
% 0.20/0.42  fof(t140_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X3,X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5)&r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6))<=>r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_tmap_1)).
% 0.20/0.42  fof(t87_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))=>![X3]:((v1_borsuk_1(X3,X1)&m1_pre_topc(X3,X1))=>r4_tsep_1(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tsep_1)).
% 0.20/0.42  fof(t144_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X3,X4))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))&r4_tsep_1(X1,X3,X4))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_tmap_1)).
% 0.20/0.42  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v1_borsuk_1(X3,X1))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_borsuk_1(X4,X1))&m1_pre_topc(X4,X1))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(((X1=k1_tsep_1(X1,X3,X4)&r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5))&r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),X1,X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))))))))))), inference(assume_negation,[status(cth)],[t152_tmap_1])).
% 0.20/0.42  fof(c_0_7, plain, ![X7, X8, X9, X10, X11, X12]:(((v1_funct_1(k10_tmap_1(X7,X8,X9,X10,X11,X12))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X7)|v2_struct_0(X10)|~m1_pre_topc(X10,X7)|~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))|~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8))))))&(v1_funct_2(k10_tmap_1(X7,X8,X9,X10,X11,X12),u1_struct_0(k1_tsep_1(X7,X9,X10)),u1_struct_0(X8))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X7)|v2_struct_0(X10)|~m1_pre_topc(X10,X7)|~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))|~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8)))))))&(m1_subset_1(k10_tmap_1(X7,X8,X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X9,X10)),u1_struct_0(X8))))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X7)|v2_struct_0(X10)|~m1_pre_topc(X10,X7)|~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))|~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).
% 0.20/0.42  fof(c_0_8, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v1_borsuk_1(esk3_0,esk1_0))&m1_pre_topc(esk3_0,esk1_0))&(((~v2_struct_0(esk4_0)&v1_borsuk_1(esk4_0,esk1_0))&m1_pre_topc(esk4_0,esk1_0))&((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(((esk1_0=k1_tsep_1(esk1_0,esk3_0,esk4_0)&r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0))&r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0))&(~v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.20/0.42  cnf(c_0_9, plain, (v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_11, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_14, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_17, negated_conjecture, (v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_22, plain, (v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  fof(c_0_23, plain, ![X25, X26, X27, X28, X29, X30]:((((v1_funct_1(k10_tmap_1(X25,X26,X27,X28,X29,X30))|~r4_tsep_1(X25,X27,X28)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X26))|~v5_pre_topc(X30,X28,X26)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~v5_pre_topc(X29,X27,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))|~r1_tsep_1(X27,X28)|(v2_struct_0(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(v1_funct_2(k10_tmap_1(X25,X26,X27,X28,X29,X30),u1_struct_0(k1_tsep_1(X25,X27,X28)),u1_struct_0(X26))|~r4_tsep_1(X25,X27,X28)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X26))|~v5_pre_topc(X30,X28,X26)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~v5_pre_topc(X29,X27,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))|~r1_tsep_1(X27,X28)|(v2_struct_0(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(v5_pre_topc(k10_tmap_1(X25,X26,X27,X28,X29,X30),k1_tsep_1(X25,X27,X28),X26)|~r4_tsep_1(X25,X27,X28)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X26))|~v5_pre_topc(X30,X28,X26)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~v5_pre_topc(X29,X27,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))|~r1_tsep_1(X27,X28)|(v2_struct_0(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(m1_subset_1(k10_tmap_1(X25,X26,X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X27,X28)),u1_struct_0(X26))))|~r4_tsep_1(X25,X27,X28)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X26))|~v5_pre_topc(X30,X28,X26)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~v5_pre_topc(X29,X27,X26)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))|~r1_tsep_1(X27,X28)|(v2_struct_0(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).
% 0.20/0.42  fof(c_0_24, plain, ![X13, X14, X15, X16, X17, X18]:((~r2_funct_2(u1_struct_0(X15),u1_struct_0(X14),k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X15,k10_tmap_1(X13,X14,X15,X16,X17,X18)),X17)|~r2_funct_2(u1_struct_0(X16),u1_struct_0(X14),k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X16,k10_tmap_1(X13,X14,X15,X16,X17,X18)),X18)|r2_funct_2(u1_struct_0(k2_tsep_1(X13,X15,X16)),u1_struct_0(X14),k3_tmap_1(X13,X14,X15,k2_tsep_1(X13,X15,X16),X17),k3_tmap_1(X13,X14,X16,k2_tsep_1(X13,X15,X16),X18))|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14)))))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14)))))|r1_tsep_1(X15,X16)|(v2_struct_0(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&((r2_funct_2(u1_struct_0(X15),u1_struct_0(X14),k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X15,k10_tmap_1(X13,X14,X15,X16,X17,X18)),X17)|~r2_funct_2(u1_struct_0(k2_tsep_1(X13,X15,X16)),u1_struct_0(X14),k3_tmap_1(X13,X14,X15,k2_tsep_1(X13,X15,X16),X17),k3_tmap_1(X13,X14,X16,k2_tsep_1(X13,X15,X16),X18))|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14)))))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14)))))|r1_tsep_1(X15,X16)|(v2_struct_0(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(r2_funct_2(u1_struct_0(X16),u1_struct_0(X14),k3_tmap_1(X13,X14,k1_tsep_1(X13,X15,X16),X16,k10_tmap_1(X13,X14,X15,X16,X17,X18)),X18)|~r2_funct_2(u1_struct_0(k2_tsep_1(X13,X15,X16)),u1_struct_0(X14),k3_tmap_1(X13,X14,X15,k2_tsep_1(X13,X15,X16),X17),k3_tmap_1(X13,X14,X16,k2_tsep_1(X13,X15,X16),X18))|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14)))))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14)))))|r1_tsep_1(X15,X16)|(v2_struct_0(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t140_tmap_1])])])])])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_31, negated_conjecture, (v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.20/0.42  cnf(c_0_32, plain, (m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_33, plain, (v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~v5_pre_topc(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~r1_tsep_1(X3,X4)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_35, plain, (r2_funct_2(u1_struct_0(k2_tsep_1(X3,X1,X4)),u1_struct_0(X2),k3_tmap_1(X3,X2,X1,k2_tsep_1(X3,X1,X4),X5),k3_tmap_1(X3,X2,X4,k2_tsep_1(X3,X1,X4),X6))|r1_tsep_1(X1,X4)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,k10_tmap_1(X3,X2,X1,X4,X5,X6)),X5)|~r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X4,k10_tmap_1(X3,X2,X1,X4,X5,X6)),X6)|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  fof(c_0_39, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~v1_borsuk_1(X32,X31)|~m1_pre_topc(X32,X31)|(~v1_borsuk_1(X33,X31)|~m1_pre_topc(X33,X31)|r4_tsep_1(X31,X32,X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t87_tsep_1])])])])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (~v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.20/0.42  cnf(c_0_44, negated_conjecture, (v5_pre_topc(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_tsep_1(X1,X2,esk4_0),esk2_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r4_tsep_1(X1,X2,esk4_0)|~v5_pre_topc(X3,X2,esk2_0)|~r1_tsep_1(X2,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_10]), c_0_34]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),X2),k3_tmap_1(esk1_0,X1,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),X3))|r1_tsep_1(esk3_0,esk4_0)|v2_struct_0(X1)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,k10_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3)),X3)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,k10_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3)),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))|~v1_funct_2(X3,u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(X1))|~v1_funct_1(X3)|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_15]), c_0_30]), c_0_21])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0)), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0)), inference(rw,[status(thm)],[c_0_38, c_0_36])).
% 0.20/0.42  cnf(c_0_49, plain, (v2_struct_0(X1)|r4_tsep_1(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_borsuk_1(X2,X1)|~m1_pre_topc(X2,X1)|~v1_borsuk_1(X3,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.42  cnf(c_0_50, negated_conjecture, (v1_borsuk_1(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_26]), c_0_36]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  fof(c_0_54, plain, ![X19, X20, X21, X22, X23, X24]:((((v1_funct_1(k10_tmap_1(X19,X20,X21,X22,X23,X24))|(~r2_funct_2(u1_struct_0(k2_tsep_1(X19,X21,X22)),u1_struct_0(X20),k3_tmap_1(X19,X20,X21,k2_tsep_1(X19,X21,X22),X23),k3_tmap_1(X19,X20,X22,k2_tsep_1(X19,X21,X22),X24))|~r4_tsep_1(X19,X21,X22))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~v5_pre_topc(X24,X22,X20)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~v5_pre_topc(X23,X21,X20)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20)))))|r1_tsep_1(X21,X22)|(v2_struct_0(X22)|~m1_pre_topc(X22,X19))|(v2_struct_0(X21)|~m1_pre_topc(X21,X19))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(v1_funct_2(k10_tmap_1(X19,X20,X21,X22,X23,X24),u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))|(~r2_funct_2(u1_struct_0(k2_tsep_1(X19,X21,X22)),u1_struct_0(X20),k3_tmap_1(X19,X20,X21,k2_tsep_1(X19,X21,X22),X23),k3_tmap_1(X19,X20,X22,k2_tsep_1(X19,X21,X22),X24))|~r4_tsep_1(X19,X21,X22))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~v5_pre_topc(X24,X22,X20)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~v5_pre_topc(X23,X21,X20)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20)))))|r1_tsep_1(X21,X22)|(v2_struct_0(X22)|~m1_pre_topc(X22,X19))|(v2_struct_0(X21)|~m1_pre_topc(X21,X19))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))))&(v5_pre_topc(k10_tmap_1(X19,X20,X21,X22,X23,X24),k1_tsep_1(X19,X21,X22),X20)|(~r2_funct_2(u1_struct_0(k2_tsep_1(X19,X21,X22)),u1_struct_0(X20),k3_tmap_1(X19,X20,X21,k2_tsep_1(X19,X21,X22),X23),k3_tmap_1(X19,X20,X22,k2_tsep_1(X19,X21,X22),X24))|~r4_tsep_1(X19,X21,X22))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~v5_pre_topc(X24,X22,X20)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~v5_pre_topc(X23,X21,X20)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20)))))|r1_tsep_1(X21,X22)|(v2_struct_0(X22)|~m1_pre_topc(X22,X19))|(v2_struct_0(X21)|~m1_pre_topc(X21,X19))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))))&(m1_subset_1(k10_tmap_1(X19,X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))))|(~r2_funct_2(u1_struct_0(k2_tsep_1(X19,X21,X22)),u1_struct_0(X20),k3_tmap_1(X19,X20,X21,k2_tsep_1(X19,X21,X22),X23),k3_tmap_1(X19,X20,X22,k2_tsep_1(X19,X21,X22),X24))|~r4_tsep_1(X19,X21,X22))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~v5_pre_topc(X24,X22,X20)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~v5_pre_topc(X23,X21,X20)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20)))))|r1_tsep_1(X21,X22)|(v2_struct_0(X22)|~m1_pre_topc(X22,X19))|(v2_struct_0(X21)|~m1_pre_topc(X21,X19))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_tmap_1])])])])])).
% 0.20/0.42  cnf(c_0_55, negated_conjecture, (v5_pre_topc(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(X1,esk3_0,esk4_0),esk2_0)|v2_struct_0(X1)|~r4_tsep_1(X1,esk3_0,esk4_0)|~r1_tsep_1(esk3_0,esk4_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_18]), c_0_45]), c_0_19]), c_0_20])]), c_0_21])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))|r1_tsep_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_10]), c_0_18]), c_0_11]), c_0_19]), c_0_12]), c_0_20]), c_0_13]), c_0_14])]), c_0_16])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (r4_tsep_1(esk1_0,X1,esk4_0)|~v1_borsuk_1(X1,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_26]), c_0_28]), c_0_29])]), c_0_30])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (v1_borsuk_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, (m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_26]), c_0_36]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.20/0.42  cnf(c_0_61, plain, (v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~v5_pre_topc(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (v5_pre_topc(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(X1,esk3_0,esk4_0),esk2_0)|r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))|v2_struct_0(X1)|~r4_tsep_1(X1,esk3_0,esk4_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (r4_tsep_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_27])])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.20/0.42  cnf(c_0_65, plain, (v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~r4_tsep_1(X1,X3,X4)|~v5_pre_topc(X6,X4,X2)|~v5_pre_topc(X5,X3,X2)|~r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[c_0_61, c_0_33])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_36]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_64]), c_0_30])).
% 0.20/0.42  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_36]), c_0_63]), c_0_34]), c_0_45]), c_0_10]), c_0_18]), c_0_11]), c_0_19]), c_0_12]), c_0_20]), c_0_26]), c_0_27]), c_0_13]), c_0_28]), c_0_14]), c_0_29])]), c_0_64]), c_0_15]), c_0_21]), c_0_16]), c_0_30]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 68
% 0.20/0.42  # Proof object clause steps            : 55
% 0.20/0.42  # Proof object formula steps           : 13
% 0.20/0.42  # Proof object conjectures             : 50
% 0.20/0.42  # Proof object clause conjectures      : 47
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 31
% 0.20/0.42  # Proof object initial formulas used   : 6
% 0.20/0.42  # Proof object generating inferences   : 18
% 0.20/0.42  # Proof object simplifying inferences  : 128
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 6
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 39
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 39
% 0.20/0.42  # Processed clauses                    : 247
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 9
% 0.20/0.42  # ...remaining for further processing  : 238
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 0
% 0.20/0.42  # Backward-rewritten                   : 5
% 0.20/0.42  # Generated clauses                    : 175
% 0.20/0.42  # ...of the previous two non-trivial   : 175
% 0.20/0.42  # Contextual simplify-reflections      : 1
% 0.20/0.42  # Paramodulations                      : 175
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 0
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 200
% 0.20/0.42  #    Positive orientable unit clauses  : 36
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 5
% 0.20/0.42  #    Non-unit-clauses                  : 159
% 0.20/0.42  # Current number of unprocessed clauses: 0
% 0.20/0.42  # ...number of literals in the above   : 0
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 38
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 14383
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 13
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 7
% 0.20/0.42  # Unit Clause-clause subsumption calls : 26
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 24
% 0.20/0.42  # BW rewrite match successes           : 4
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 27692
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.072 s
% 0.20/0.42  # System time              : 0.006 s
% 0.20/0.42  # Total time               : 0.078 s
% 0.20/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

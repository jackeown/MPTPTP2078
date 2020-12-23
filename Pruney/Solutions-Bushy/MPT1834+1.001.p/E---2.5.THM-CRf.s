%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1834+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:51 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 (7116 expanded)
%              Number of clauses        :   79 (2006 expanded)
%              Number of leaves         :    7 (1780 expanded)
%              Depth                    :   26
%              Number of atoms          : 1290 (294098 expanded)
%              Number of equality atoms :    6 (  66 expanded)
%              Maximal formula depth    :   40 (  10 average)
%              Maximal clause size      :  254 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t150_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r3_tsep_1(X1,X2,X3)
              <=> ( r1_tsep_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v2_struct_0(X4)
                        & v2_pre_topc(X4)
                        & l1_pre_topc(X4) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
                            & v5_pre_topc(X5,X2,X4)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4))
                                & v5_pre_topc(X6,X3,X4)
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                             => ( v1_funct_1(k10_tmap_1(X1,X4,X2,X3,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X4,X2,X3,X5,X6),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                                & v5_pre_topc(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_tsep_1(X1,X2,X3),X4)
                                & m1_subset_1(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_tmap_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t138_tmap_1,axiom,(
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
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).

fof(t135_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r3_tsep_1(X1,X2,X3)
              <=> ( r1_tsep_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v2_struct_0(X4)
                        & v2_pre_topc(X4)
                        & l1_pre_topc(X4) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) )
                         => ( ( v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5))
                              & v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),u1_struct_0(X2),u1_struct_0(X4))
                              & v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X2,X4)
                              & m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
                              & v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5))
                              & v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),u1_struct_0(X3),u1_struct_0(X4))
                              & v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X3,X4)
                              & m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                           => ( v1_funct_1(X5)
                              & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                              & v5_pre_topc(X5,k1_tsep_1(X1,X2,X3),X4)
                              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_tmap_1)).

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

fof(t85_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ( r1_tsep_1(X2,X3)
                  & r4_tsep_1(X1,X2,X3) )
              <=> r3_tsep_1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tsep_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r3_tsep_1(X1,X2,X3)
                <=> ( r1_tsep_1(X2,X3)
                    & ! [X4] :
                        ( ( ~ v2_struct_0(X4)
                          & v2_pre_topc(X4)
                          & l1_pre_topc(X4) )
                       => ! [X5] :
                            ( ( v1_funct_1(X5)
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
                              & v5_pre_topc(X5,X2,X4)
                              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))) )
                           => ! [X6] :
                                ( ( v1_funct_1(X6)
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4))
                                  & v5_pre_topc(X6,X3,X4)
                                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                               => ( v1_funct_1(k10_tmap_1(X1,X4,X2,X3,X5,X6))
                                  & v1_funct_2(k10_tmap_1(X1,X4,X2,X3,X5,X6),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                                  & v5_pre_topc(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_tsep_1(X1,X2,X3),X4)
                                  & m1_subset_1(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t150_tmap_1])).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_funct_2(X19,X20,X21,X22)
        | X21 = X22
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != X22
        | r2_funct_2(X19,X20,X21,X22)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

fof(c_0_9,negated_conjecture,(
    ! [X55,X56,X57] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk3_0)
      & ( ~ v2_struct_0(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v2_pre_topc(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( l1_pre_topc(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(esk7_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(esk7_0,esk4_0,esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(esk8_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(esk8_0,esk5_0,esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))
        | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
        | ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
        | ~ m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( r1_tsep_1(esk4_0,esk5_0)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(k10_tmap_1(esk3_0,X55,esk4_0,esk5_0,X56,X57))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(esk5_0),u1_struct_0(X55))
        | ~ v5_pre_topc(X57,esk5_0,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X55))))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(esk4_0),u1_struct_0(X55))
        | ~ v5_pre_topc(X56,esk4_0,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X55))))
        | v2_struct_0(X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(k10_tmap_1(esk3_0,X55,esk4_0,esk5_0,X56,X57),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X55))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(esk5_0),u1_struct_0(X55))
        | ~ v5_pre_topc(X57,esk5_0,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X55))))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(esk4_0),u1_struct_0(X55))
        | ~ v5_pre_topc(X56,esk4_0,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X55))))
        | v2_struct_0(X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(k10_tmap_1(esk3_0,X55,esk4_0,esk5_0,X56,X57),k1_tsep_1(esk3_0,esk4_0,esk5_0),X55)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(esk5_0),u1_struct_0(X55))
        | ~ v5_pre_topc(X57,esk5_0,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X55))))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(esk4_0),u1_struct_0(X55))
        | ~ v5_pre_topc(X56,esk4_0,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X55))))
        | v2_struct_0(X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(k10_tmap_1(esk3_0,X55,esk4_0,esk5_0,X56,X57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X55))))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,u1_struct_0(esk5_0),u1_struct_0(X55))
        | ~ v5_pre_topc(X57,esk5_0,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X55))))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,u1_struct_0(esk4_0),u1_struct_0(X55))
        | ~ v5_pre_topc(X56,esk4_0,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X55))))
        | v2_struct_0(X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

cnf(c_0_10,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X3,esk5_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X2,esk4_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3))
    | v2_struct_0(X1)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X3,esk5_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X2,esk4_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))
    | v2_struct_0(X1)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X3,esk5_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X2,esk4_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ m1_pre_topc(X37,X35)
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X35)
      | ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,u1_struct_0(k1_tsep_1(X35,X37,X38)),u1_struct_0(X36))
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X35,X37,X38)),u1_struct_0(X36))))
      | r2_funct_2(u1_struct_0(k1_tsep_1(X35,X37,X38)),u1_struct_0(X36),X39,k10_tmap_1(X35,X36,X37,X38,k3_tmap_1(X35,X36,k1_tsep_1(X35,X37,X38),X37,X39),k3_tmap_1(X35,X36,k1_tsep_1(X35,X37,X38),X38,X39))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t138_tmap_1])])])])).

cnf(c_0_15,negated_conjecture,
    ( X1 = k10_tmap_1(esk3_0,X2,esk4_0,esk5_0,X3,X4)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(X4,esk5_0,X2)
    | ~ v5_pre_topc(X3,esk4_0,X2)
    | ~ r2_funct_2(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2),X1,k10_tmap_1(esk3_0,X2,esk4_0,esk5_0,X3,X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))
    | ~ v1_funct_2(X4,u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( v5_pre_topc(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3),k1_tsep_1(esk3_0,esk4_0,esk5_0),X1)
    | v2_struct_0(X1)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X3,esk5_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X2,esk4_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2)) = X2
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(X1)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2),esk5_0,X1)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),esk4_0,X1)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23])).

fof(c_0_26,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ( r1_tsep_1(X29,X30)
        | ~ r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_funct_1(X32)
        | ~ v1_funct_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32))
        | ~ v1_funct_2(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),u1_struct_0(X29),u1_struct_0(X31))
        | ~ v5_pre_topc(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),X29,X31)
        | ~ m1_subset_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X31))))
        | ~ v1_funct_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32))
        | ~ v1_funct_2(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),u1_struct_0(X30),u1_struct_0(X31))
        | ~ v5_pre_topc(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),X30,X31)
        | ~ m1_subset_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_funct_2(X32,u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))
        | ~ v1_funct_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32))
        | ~ v1_funct_2(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),u1_struct_0(X29),u1_struct_0(X31))
        | ~ v5_pre_topc(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),X29,X31)
        | ~ m1_subset_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X31))))
        | ~ v1_funct_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32))
        | ~ v1_funct_2(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),u1_struct_0(X30),u1_struct_0(X31))
        | ~ v5_pre_topc(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),X30,X31)
        | ~ m1_subset_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v5_pre_topc(X32,k1_tsep_1(X28,X29,X30),X31)
        | ~ v1_funct_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32))
        | ~ v1_funct_2(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),u1_struct_0(X29),u1_struct_0(X31))
        | ~ v5_pre_topc(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),X29,X31)
        | ~ m1_subset_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X31))))
        | ~ v1_funct_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32))
        | ~ v1_funct_2(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),u1_struct_0(X30),u1_struct_0(X31))
        | ~ v5_pre_topc(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),X30,X31)
        | ~ m1_subset_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))))
        | ~ v1_funct_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32))
        | ~ v1_funct_2(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),u1_struct_0(X29),u1_struct_0(X31))
        | ~ v5_pre_topc(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),X29,X31)
        | ~ m1_subset_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X29,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X31))))
        | ~ v1_funct_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32))
        | ~ v1_funct_2(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),u1_struct_0(X30),u1_struct_0(X31))
        | ~ v5_pre_topc(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),X30,X31)
        | ~ m1_subset_1(k3_tmap_1(X28,X31,k1_tsep_1(X28,X29,X30),X30,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(X31))))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v2_struct_0(esk1_3(X28,X29,X30))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v2_pre_topc(esk1_3(X28,X29,X30))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( l1_pre_topc(esk1_3(X28,X29,X30))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_funct_1(esk2_3(X28,X29,X30))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_funct_2(esk2_3(X28,X29,X30),u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(esk1_3(X28,X29,X30)))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk2_3(X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(esk1_3(X28,X29,X30)))))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_funct_1(k3_tmap_1(X28,esk1_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),X29,esk2_3(X28,X29,X30)))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_funct_2(k3_tmap_1(X28,esk1_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),X29,esk2_3(X28,X29,X30)),u1_struct_0(X29),u1_struct_0(esk1_3(X28,X29,X30)))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v5_pre_topc(k3_tmap_1(X28,esk1_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),X29,esk2_3(X28,X29,X30)),X29,esk1_3(X28,X29,X30))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(k3_tmap_1(X28,esk1_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),X29,esk2_3(X28,X29,X30)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(esk1_3(X28,X29,X30)))))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_funct_1(k3_tmap_1(X28,esk1_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),X30,esk2_3(X28,X29,X30)))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v1_funct_2(k3_tmap_1(X28,esk1_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),X30,esk2_3(X28,X29,X30)),u1_struct_0(X30),u1_struct_0(esk1_3(X28,X29,X30)))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v5_pre_topc(k3_tmap_1(X28,esk1_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),X30,esk2_3(X28,X29,X30)),X30,esk1_3(X28,X29,X30))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(k3_tmap_1(X28,esk1_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),X30,esk2_3(X28,X29,X30)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(esk1_3(X28,X29,X30)))))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v1_funct_1(esk2_3(X28,X29,X30))
        | ~ v1_funct_2(esk2_3(X28,X29,X30),u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(esk1_3(X28,X29,X30)))
        | ~ v5_pre_topc(esk2_3(X28,X29,X30),k1_tsep_1(X28,X29,X30),esk1_3(X28,X29,X30))
        | ~ m1_subset_1(esk2_3(X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X29,X30)),u1_struct_0(esk1_3(X28,X29,X30)))))
        | ~ r1_tsep_1(X29,X30)
        | r3_tsep_1(X28,X29,X30)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t135_tmap_1])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( v5_pre_topc(X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),X2)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),esk5_0,X2)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),esk4_0,X2)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_31,plain,
    ( m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_33,plain,
    ( v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_35,plain,
    ( v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_37,plain,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),X3,esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_39,plain,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),X2,esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_43,plain,
    ( v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(esk2_3(X1,X2,X3))
    | ~ v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( v1_funct_1(esk2_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,plain,
    ( v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_48,plain,
    ( v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_49,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ r1_tsep_1(X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_53,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_45]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_54,plain,
    ( v2_pre_topc(esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_55,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( v1_funct_1(k10_tmap_1(X10,X11,X12,X13,X14,X15))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X10)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X11))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X11)))) )
      & ( v1_funct_2(k10_tmap_1(X10,X11,X12,X13,X14,X15),u1_struct_0(k1_tsep_1(X10,X12,X13)),u1_struct_0(X11))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X10)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X11))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X11)))) )
      & ( m1_subset_1(k10_tmap_1(X10,X11,X12,X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X10,X12,X13)),u1_struct_0(X11))))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,X10)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X10)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X11))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X11)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

cnf(c_0_56,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_57,plain,
    ( l1_pre_topc(esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))
    | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
    | ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_61,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk7_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk8_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_69,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk1_3(X1,X2,X3))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_71,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_72,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_73,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ( v1_funct_1(k10_tmap_1(X40,X41,X42,X43,X44,X45))
        | ~ r4_tsep_1(X40,X42,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(X43),u1_struct_0(X41))
        | ~ v5_pre_topc(X45,X43,X41)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X41))))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,u1_struct_0(X42),u1_struct_0(X41))
        | ~ v5_pre_topc(X44,X42,X41)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41))))
        | ~ r1_tsep_1(X42,X43)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X40)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X40)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v1_funct_2(k10_tmap_1(X40,X41,X42,X43,X44,X45),u1_struct_0(k1_tsep_1(X40,X42,X43)),u1_struct_0(X41))
        | ~ r4_tsep_1(X40,X42,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(X43),u1_struct_0(X41))
        | ~ v5_pre_topc(X45,X43,X41)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X41))))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,u1_struct_0(X42),u1_struct_0(X41))
        | ~ v5_pre_topc(X44,X42,X41)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41))))
        | ~ r1_tsep_1(X42,X43)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X40)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X40)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v5_pre_topc(k10_tmap_1(X40,X41,X42,X43,X44,X45),k1_tsep_1(X40,X42,X43),X41)
        | ~ r4_tsep_1(X40,X42,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(X43),u1_struct_0(X41))
        | ~ v5_pre_topc(X45,X43,X41)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X41))))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,u1_struct_0(X42),u1_struct_0(X41))
        | ~ v5_pre_topc(X44,X42,X41)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41))))
        | ~ r1_tsep_1(X42,X43)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X40)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X40)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(k10_tmap_1(X40,X41,X42,X43,X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X42,X43)),u1_struct_0(X41))))
        | ~ r4_tsep_1(X40,X42,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(X43),u1_struct_0(X41))
        | ~ v5_pre_topc(X45,X43,X41)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X41))))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,u1_struct_0(X42),u1_struct_0(X41))
        | ~ v5_pre_topc(X44,X42,X41)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41))))
        | ~ r1_tsep_1(X42,X43)
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X43,X40)
        | v2_struct_0(X42)
        | ~ m1_pre_topc(X42,X40)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_75,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r3_tsep_1(X3,X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_76,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_78,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk4_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_80,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk5_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(X1,esk6_0,X2,esk5_0,X3,esk8_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk6_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk6_0))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_67]),c_0_21]),c_0_60]),c_0_61]),c_0_63]),c_0_65]),c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_23]),c_0_21]),c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( ~ r4_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_79]),c_0_80]),c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(X1,esk6_0,X2,esk5_0,X3,esk8_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk6_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk6_0))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_76])]),c_0_82])])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_76])]),c_0_82])])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_76])]),c_0_82])])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_76])]),c_0_82])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r4_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_76])]),c_0_82])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(X1,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87])]),c_0_22])).

fof(c_0_90,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r1_tsep_1(X47,X48)
        | ~ r4_tsep_1(X46,X47,X48)
        | r3_tsep_1(X46,X47,X48)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( r1_tsep_1(X47,X48)
        | ~ r3_tsep_1(X46,X47,X48)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( r4_tsep_1(X46,X47,X48)
        | ~ r3_tsep_1(X46,X47,X48)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t85_tsep_1])])])])])).

cnf(c_0_91,negated_conjecture,
    ( ~ r4_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_23])).

cnf(c_0_92,plain,
    ( r4_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_tsep_1(X1,X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_76]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------

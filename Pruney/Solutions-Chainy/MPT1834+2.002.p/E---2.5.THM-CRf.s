%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 (1555 expanded)
%              Number of clauses        :   73 ( 434 expanded)
%              Number of leaves         :    7 ( 389 expanded)
%              Depth                    :   23
%              Number of atoms          : 1261 (63049 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   40 (  11 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tsep_1)).

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
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_funct_2(X7,X8,X9,X10)
        | X9 = X10
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X9 != X10
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

fof(c_0_9,negated_conjecture,(
    ! [X44,X45,X46] :
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
      & ( v1_funct_1(k10_tmap_1(esk3_0,X44,esk4_0,esk5_0,X45,X46))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(esk5_0),u1_struct_0(X44))
        | ~ v5_pre_topc(X46,esk5_0,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X44))))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(esk4_0),u1_struct_0(X44))
        | ~ v5_pre_topc(X45,esk4_0,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X44))))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(k10_tmap_1(esk3_0,X44,esk4_0,esk5_0,X45,X46),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X44))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(esk5_0),u1_struct_0(X44))
        | ~ v5_pre_topc(X46,esk5_0,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X44))))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(esk4_0),u1_struct_0(X44))
        | ~ v5_pre_topc(X45,esk4_0,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X44))))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(k10_tmap_1(esk3_0,X44,esk4_0,esk5_0,X45,X46),k1_tsep_1(esk3_0,esk4_0,esk5_0),X44)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(esk5_0),u1_struct_0(X44))
        | ~ v5_pre_topc(X46,esk5_0,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X44))))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(esk4_0),u1_struct_0(X44))
        | ~ v5_pre_topc(X45,esk4_0,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X44))))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(k10_tmap_1(esk3_0,X44,esk4_0,esk5_0,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X44))))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(esk5_0),u1_struct_0(X44))
        | ~ v5_pre_topc(X46,esk5_0,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X44))))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,u1_struct_0(esk4_0),u1_struct_0(X44))
        | ~ v5_pre_topc(X45,esk4_0,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X44))))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
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
    ! [X24,X25,X26,X27,X28] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X24)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X24)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,u1_struct_0(k1_tsep_1(X24,X26,X27)),u1_struct_0(X25))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X24,X26,X27)),u1_struct_0(X25))))
      | r2_funct_2(u1_struct_0(k1_tsep_1(X24,X26,X27)),u1_struct_0(X25),X28,k10_tmap_1(X24,X25,X26,X27,k3_tmap_1(X24,X25,k1_tsep_1(X24,X26,X27),X26,X28),k3_tmap_1(X24,X25,k1_tsep_1(X24,X26,X27),X27,X28))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t138_tmap_1])])])])).

cnf(c_0_15,negated_conjecture,
    ( X1 = k10_tmap_1(esk3_0,X2,esk4_0,esk5_0,X3,X4)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(X4,esk5_0,X2)
    | ~ v5_pre_topc(X3,esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ r2_funct_2(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2),X1,k10_tmap_1(esk3_0,X2,esk4_0,esk5_0,X3,X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))
    | ~ v1_funct_2(X4,u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3) ),
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
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
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
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23])).

fof(c_0_26,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( r1_tsep_1(X18,X19)
        | ~ r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_funct_1(X21)
        | ~ v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21))
        | ~ v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),u1_struct_0(X18),u1_struct_0(X20))
        | ~ v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),X18,X20)
        | ~ m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X20))))
        | ~ v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21))
        | ~ v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),u1_struct_0(X19),u1_struct_0(X20))
        | ~ v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),X19,X20)
        | ~ m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))
        | ~ v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21))
        | ~ v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),u1_struct_0(X18),u1_struct_0(X20))
        | ~ v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),X18,X20)
        | ~ m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X20))))
        | ~ v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21))
        | ~ v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),u1_struct_0(X19),u1_struct_0(X20))
        | ~ v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),X19,X20)
        | ~ m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v5_pre_topc(X21,k1_tsep_1(X17,X18,X19),X20)
        | ~ v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21))
        | ~ v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),u1_struct_0(X18),u1_struct_0(X20))
        | ~ v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),X18,X20)
        | ~ m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X20))))
        | ~ v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21))
        | ~ v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),u1_struct_0(X19),u1_struct_0(X20))
        | ~ v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),X19,X20)
        | ~ m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))))
        | ~ v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21))
        | ~ v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),u1_struct_0(X18),u1_struct_0(X20))
        | ~ v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),X18,X20)
        | ~ m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X20))))
        | ~ v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21))
        | ~ v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),u1_struct_0(X19),u1_struct_0(X20))
        | ~ v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),X19,X20)
        | ~ m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ v2_struct_0(esk1_3(X17,X18,X19))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v2_pre_topc(esk1_3(X17,X18,X19))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( l1_pre_topc(esk1_3(X17,X18,X19))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_funct_1(esk2_3(X17,X18,X19))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_funct_2(esk2_3(X17,X18,X19),u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(esk1_3(X17,X18,X19)))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(esk1_3(X17,X18,X19)))))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_funct_1(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X18,esk2_3(X17,X18,X19)))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_funct_2(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X18,esk2_3(X17,X18,X19)),u1_struct_0(X18),u1_struct_0(esk1_3(X17,X18,X19)))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v5_pre_topc(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X18,esk2_3(X17,X18,X19)),X18,esk1_3(X17,X18,X19))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X18,esk2_3(X17,X18,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(esk1_3(X17,X18,X19)))))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_funct_1(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X19,esk2_3(X17,X18,X19)))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v1_funct_2(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X19,esk2_3(X17,X18,X19)),u1_struct_0(X19),u1_struct_0(esk1_3(X17,X18,X19)))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( v5_pre_topc(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X19,esk2_3(X17,X18,X19)),X19,esk1_3(X17,X18,X19))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X19,esk2_3(X17,X18,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(esk1_3(X17,X18,X19)))))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ v1_funct_1(esk2_3(X17,X18,X19))
        | ~ v1_funct_2(esk2_3(X17,X18,X19),u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(esk1_3(X17,X18,X19)))
        | ~ v5_pre_topc(esk2_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),esk1_3(X17,X18,X19))
        | ~ m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(esk1_3(X17,X18,X19)))))
        | ~ r1_tsep_1(X18,X19)
        | r3_tsep_1(X17,X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t135_tmap_1])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( v5_pre_topc(X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),X2)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),esk5_0,X2)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1))
    | ~ v1_funct_1(X1) ),
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
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
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
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
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
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
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
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
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
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
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
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
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
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
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
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
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

fof(c_0_49,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( v1_funct_1(k10_tmap_1(X11,X12,X13,X14,X15,X16))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))) )
      & ( v1_funct_2(k10_tmap_1(X11,X12,X13,X14,X15,X16),u1_struct_0(k1_tsep_1(X11,X13,X14)),u1_struct_0(X12))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))) )
      & ( m1_subset_1(k10_tmap_1(X11,X12,X13,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X11,X13,X14)),u1_struct_0(X12))))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

cnf(c_0_50,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))
    | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
    | ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk7_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(esk8_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_63,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_65,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_66,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ( v1_funct_1(k10_tmap_1(X29,X30,X31,X32,X33,X34))
        | ~ r4_tsep_1(X29,X31,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X30))
        | ~ v5_pre_topc(X34,X32,X30)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))
        | ~ v5_pre_topc(X33,X31,X30)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))
        | ~ r1_tsep_1(X31,X32)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_2(k10_tmap_1(X29,X30,X31,X32,X33,X34),u1_struct_0(k1_tsep_1(X29,X31,X32)),u1_struct_0(X30))
        | ~ r4_tsep_1(X29,X31,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X30))
        | ~ v5_pre_topc(X34,X32,X30)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))
        | ~ v5_pre_topc(X33,X31,X30)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))
        | ~ r1_tsep_1(X31,X32)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v5_pre_topc(k10_tmap_1(X29,X30,X31,X32,X33,X34),k1_tsep_1(X29,X31,X32),X30)
        | ~ r4_tsep_1(X29,X31,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X30))
        | ~ v5_pre_topc(X34,X32,X30)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))
        | ~ v5_pre_topc(X33,X31,X30)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))
        | ~ r1_tsep_1(X31,X32)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(k10_tmap_1(X29,X30,X31,X32,X33,X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X31,X32)),u1_struct_0(X30))))
        | ~ r4_tsep_1(X29,X31,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X30))
        | ~ v5_pre_topc(X34,X32,X30)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))
        | ~ v5_pre_topc(X33,X31,X30)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))
        | ~ r1_tsep_1(X31,X32)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).

cnf(c_0_67,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_46]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_68,plain,
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

cnf(c_0_69,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_70,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk4_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_72,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk5_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_73,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_74,plain,
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

cnf(c_0_75,negated_conjecture,
    ( ~ r4_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_71]),c_0_72]),c_0_62])).

cnf(c_0_76,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_77,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r1_tsep_1(X36,X37)
        | ~ r4_tsep_1(X35,X36,X37)
        | r3_tsep_1(X35,X36,X37)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r1_tsep_1(X36,X37)
        | ~ r3_tsep_1(X35,X36,X37)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r4_tsep_1(X35,X36,X37)
        | ~ r3_tsep_1(X35,X36,X37)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X35)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t85_tsep_1])])])])])).

cnf(c_0_78,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_79,negated_conjecture,
    ( ~ r4_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_80,plain,
    ( r4_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_tsep_1(X1,X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_81,plain,
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

cnf(c_0_82,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_45]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_84,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22]),c_0_23]),c_0_29])).

cnf(c_0_85,plain,
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

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_23]),c_0_21]),c_0_22]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:40:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039N
% 0.19/0.39  # and selection function PSelectUnlessUniqMaxPos.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.033 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t150_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(X5,X2,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(k10_tmap_1(X1,X4,X2,X3,X5,X6))&v1_funct_2(k10_tmap_1(X1,X4,X2,X3,X5,X6),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&v5_pre_topc(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_tsep_1(X1,X2,X3),X4))&m1_subset_1(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_tmap_1)).
% 0.19/0.40  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.19/0.40  fof(t138_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_tmap_1)).
% 0.19/0.40  fof(t135_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))))=>((((((((v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5))&v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X2,X4))&m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))&v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5)))&v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X3,X4))&m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&v5_pre_topc(X5,k1_tsep_1(X1,X2,X3),X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_tmap_1)).
% 0.19/0.40  fof(dt_k10_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(X6))&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 0.19/0.40  fof(t145_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r1_tsep_1(X3,X4)=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(r4_tsep_1(X1,X3,X4)=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_tmap_1)).
% 0.19/0.40  fof(t85_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>((r1_tsep_1(X2,X3)&r4_tsep_1(X1,X2,X3))<=>r3_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tsep_1)).
% 0.19/0.40  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(X5,X2,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(k10_tmap_1(X1,X4,X2,X3,X5,X6))&v1_funct_2(k10_tmap_1(X1,X4,X2,X3,X5,X6),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&v5_pre_topc(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_tsep_1(X1,X2,X3),X4))&m1_subset_1(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))))))))))))), inference(assume_negation,[status(cth)],[t150_tmap_1])).
% 0.19/0.40  fof(c_0_8, plain, ![X7, X8, X9, X10]:((~r2_funct_2(X7,X8,X9,X10)|X9=X10|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(X9!=X10|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.19/0.40  fof(c_0_9, negated_conjecture, ![X44, X45, X46]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&(((((~v2_struct_0(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v2_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(l1_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(((((v1_funct_1(esk7_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(esk7_0,esk4_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(((((v1_funct_1(esk8_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(esk8_0,esk5_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))|~v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))|~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))))&((r1_tsep_1(esk4_0,esk5_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0))&((((v1_funct_1(k10_tmap_1(esk3_0,X44,esk4_0,esk5_0,X45,X46))|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(esk5_0),u1_struct_0(X44))|~v5_pre_topc(X46,esk5_0,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X44)))))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(esk4_0),u1_struct_0(X44))|~v5_pre_topc(X45,esk4_0,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X44)))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))|r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(k10_tmap_1(esk3_0,X44,esk4_0,esk5_0,X45,X46),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X44))|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(esk5_0),u1_struct_0(X44))|~v5_pre_topc(X46,esk5_0,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X44)))))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(esk4_0),u1_struct_0(X44))|~v5_pre_topc(X45,esk4_0,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X44)))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))|r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(k10_tmap_1(esk3_0,X44,esk4_0,esk5_0,X45,X46),k1_tsep_1(esk3_0,esk4_0,esk5_0),X44)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(esk5_0),u1_struct_0(X44))|~v5_pre_topc(X46,esk5_0,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X44)))))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(esk4_0),u1_struct_0(X44))|~v5_pre_topc(X45,esk4_0,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X44)))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))|r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(k10_tmap_1(esk3_0,X44,esk4_0,esk5_0,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X44))))|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(esk5_0),u1_struct_0(X44))|~v5_pre_topc(X46,esk5_0,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X44)))))|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(esk4_0),u1_struct_0(X44))|~v5_pre_topc(X45,esk4_0,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X44)))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))|r3_tsep_1(esk3_0,esk4_0,esk5_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).
% 0.19/0.40  cnf(c_0_10, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_11, negated_conjecture, (m1_subset_1(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))))|v2_struct_0(X1)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))|~v5_pre_topc(X3,esk5_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~v1_funct_1(X2)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v5_pre_topc(X2,esk4_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_12, negated_conjecture, (v1_funct_1(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3))|v2_struct_0(X1)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))|~v5_pre_topc(X3,esk5_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~v1_funct_1(X2)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v5_pre_topc(X2,esk4_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_13, negated_conjecture, (v1_funct_2(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))|v2_struct_0(X1)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))|~v5_pre_topc(X3,esk5_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~v1_funct_1(X2)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v5_pre_topc(X2,esk4_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  fof(c_0_14, plain, ![X24, X25, X26, X27, X28]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~m1_pre_topc(X26,X24)|(v2_struct_0(X27)|~m1_pre_topc(X27,X24)|(~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(k1_tsep_1(X24,X26,X27)),u1_struct_0(X25))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X24,X26,X27)),u1_struct_0(X25))))|r2_funct_2(u1_struct_0(k1_tsep_1(X24,X26,X27)),u1_struct_0(X25),X28,k10_tmap_1(X24,X25,X26,X27,k3_tmap_1(X24,X25,k1_tsep_1(X24,X26,X27),X26,X28),k3_tmap_1(X24,X25,k1_tsep_1(X24,X26,X27),X27,X28)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t138_tmap_1])])])])).
% 0.19/0.40  cnf(c_0_15, negated_conjecture, (X1=k10_tmap_1(esk3_0,X2,esk4_0,esk5_0,X3,X4)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(X2)|~v5_pre_topc(X4,esk5_0,X2)|~v5_pre_topc(X3,esk4_0,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~r2_funct_2(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2),X1,k10_tmap_1(esk3_0,X2,esk4_0,esk5_0,X3,X4))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~v1_funct_2(X1,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))|~v1_funct_2(X4,u1_struct_0(esk5_0),u1_struct_0(X2))|~v1_funct_2(X3,u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_1(X1)|~v1_funct_1(X4)|~v1_funct_1(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])).
% 0.19/0.40  cnf(c_0_16, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (v5_pre_topc(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3),k1_tsep_1(esk3_0,esk4_0,esk5_0),X1)|v2_struct_0(X1)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))|~v5_pre_topc(X3,esk5_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~v1_funct_1(X2)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v5_pre_topc(X2,esk4_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2))=X2|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(X1)|~v5_pre_topc(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2),esk5_0,X1)|~v5_pre_topc(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~m1_subset_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))))|~v1_funct_2(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_2(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2),u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_2(X2,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X1))|~v1_funct_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X2))|~v1_funct_1(k3_tmap_1(esk3_0,X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X2))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23])).
% 0.19/0.40  fof(c_0_26, plain, ![X17, X18, X19, X20, X21]:(((r1_tsep_1(X18,X19)|~r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((((v1_funct_1(X21)|(~v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21))|~v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),u1_struct_0(X18),u1_struct_0(X20))|~v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),X18,X20)|~m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X20))))|~v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21))|~v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),u1_struct_0(X19),u1_struct_0(X20))|~v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),X19,X20)|~m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|~r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))|(~v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21))|~v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),u1_struct_0(X18),u1_struct_0(X20))|~v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),X18,X20)|~m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X20))))|~v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21))|~v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),u1_struct_0(X19),u1_struct_0(X20))|~v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),X19,X20)|~m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|~r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(v5_pre_topc(X21,k1_tsep_1(X17,X18,X19),X20)|(~v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21))|~v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),u1_struct_0(X18),u1_struct_0(X20))|~v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),X18,X20)|~m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X20))))|~v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21))|~v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),u1_struct_0(X19),u1_struct_0(X20))|~v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),X19,X20)|~m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|~r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))))|(~v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21))|~v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),u1_struct_0(X18),u1_struct_0(X20))|~v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),X18,X20)|~m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X18,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X20))))|~v1_funct_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21))|~v1_funct_2(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),u1_struct_0(X19),u1_struct_0(X20))|~v5_pre_topc(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),X19,X20)|~m1_subset_1(k3_tmap_1(X17,X20,k1_tsep_1(X17,X18,X19),X19,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(X20)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|~r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))))&((((~v2_struct_0(esk1_3(X17,X18,X19))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(v2_pre_topc(esk1_3(X17,X18,X19))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(l1_pre_topc(esk1_3(X17,X18,X19))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&((((v1_funct_1(esk2_3(X17,X18,X19))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(v1_funct_2(esk2_3(X17,X18,X19),u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(esk1_3(X17,X18,X19)))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(esk1_3(X17,X18,X19)))))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(((((((((v1_funct_1(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X18,esk2_3(X17,X18,X19)))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(v1_funct_2(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X18,esk2_3(X17,X18,X19)),u1_struct_0(X18),u1_struct_0(esk1_3(X17,X18,X19)))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(v5_pre_topc(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X18,esk2_3(X17,X18,X19)),X18,esk1_3(X17,X18,X19))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(m1_subset_1(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X18,esk2_3(X17,X18,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(esk1_3(X17,X18,X19)))))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(v1_funct_1(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X19,esk2_3(X17,X18,X19)))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(v1_funct_2(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X19,esk2_3(X17,X18,X19)),u1_struct_0(X19),u1_struct_0(esk1_3(X17,X18,X19)))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(v5_pre_topc(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X19,esk2_3(X17,X18,X19)),X19,esk1_3(X17,X18,X19))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(m1_subset_1(k3_tmap_1(X17,esk1_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),X19,esk2_3(X17,X18,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(esk1_3(X17,X18,X19)))))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))&(~v1_funct_1(esk2_3(X17,X18,X19))|~v1_funct_2(esk2_3(X17,X18,X19),u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(esk1_3(X17,X18,X19)))|~v5_pre_topc(esk2_3(X17,X18,X19),k1_tsep_1(X17,X18,X19),esk1_3(X17,X18,X19))|~m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X17,X18,X19)),u1_struct_0(esk1_3(X17,X18,X19)))))|~r1_tsep_1(X18,X19)|r3_tsep_1(X17,X18,X19)|(v2_struct_0(X19)|~m1_pre_topc(X19,X17))|(v2_struct_0(X18)|~m1_pre_topc(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t135_tmap_1])])])])])])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (v5_pre_topc(X1,k1_tsep_1(esk3_0,esk4_0,esk5_0),X2)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(X2)|~v5_pre_topc(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),esk5_0,X2)|~v5_pre_topc(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),esk4_0,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))|~m1_subset_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))))|~v1_funct_2(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))|~v1_funct_2(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_2(X1,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X2))|~v1_funct_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,X1))|~v1_funct_1(k3_tmap_1(esk3_0,X2,k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,X1))|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  cnf(c_0_28, plain, (m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (r1_tsep_1(esk4_0,esk5_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_31, plain, (m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_33, plain, (v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_35, plain, (v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_37, plain, (v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),X3,esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_39, plain, (v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),X2,esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_41, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_43, plain, (v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_44, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(esk2_3(X1,X2,X3))|~v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))|~v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))|~m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_45, plain, (v1_funct_1(esk2_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_46, plain, (v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_48, plain, (v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  fof(c_0_49, plain, ![X11, X12, X13, X14, X15, X16]:(((v1_funct_1(k10_tmap_1(X11,X12,X13,X14,X15,X16))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X11)|v2_struct_0(X14)|~m1_pre_topc(X14,X11)|~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))|~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12))))))&(v1_funct_2(k10_tmap_1(X11,X12,X13,X14,X15,X16),u1_struct_0(k1_tsep_1(X11,X13,X14)),u1_struct_0(X12))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X11)|v2_struct_0(X14)|~m1_pre_topc(X14,X11)|~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))|~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))))))&(m1_subset_1(k10_tmap_1(X11,X12,X13,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X11,X13,X14)),u1_struct_0(X12))))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X11)|v2_struct_0(X14)|~m1_pre_topc(X14,X11)|~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))|~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).
% 0.19/0.40  cnf(c_0_50, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_41])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))|~v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))|~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_53, plain, (m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk7_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (v1_funct_1(esk8_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (v2_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (l1_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))|~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61]), c_0_62])).
% 0.19/0.40  cnf(c_0_65, plain, (v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  fof(c_0_66, plain, ![X29, X30, X31, X32, X33, X34]:((((v1_funct_1(k10_tmap_1(X29,X30,X31,X32,X33,X34))|~r4_tsep_1(X29,X31,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X30))|~v5_pre_topc(X34,X32,X30)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30)))))|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))|~v5_pre_topc(X33,X31,X30)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30)))))|~r1_tsep_1(X31,X32)|(v2_struct_0(X32)|~m1_pre_topc(X32,X29))|(v2_struct_0(X31)|~m1_pre_topc(X31,X29))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(v1_funct_2(k10_tmap_1(X29,X30,X31,X32,X33,X34),u1_struct_0(k1_tsep_1(X29,X31,X32)),u1_struct_0(X30))|~r4_tsep_1(X29,X31,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X30))|~v5_pre_topc(X34,X32,X30)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30)))))|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))|~v5_pre_topc(X33,X31,X30)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30)))))|~r1_tsep_1(X31,X32)|(v2_struct_0(X32)|~m1_pre_topc(X32,X29))|(v2_struct_0(X31)|~m1_pre_topc(X31,X29))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))))&(v5_pre_topc(k10_tmap_1(X29,X30,X31,X32,X33,X34),k1_tsep_1(X29,X31,X32),X30)|~r4_tsep_1(X29,X31,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X30))|~v5_pre_topc(X34,X32,X30)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30)))))|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))|~v5_pre_topc(X33,X31,X30)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30)))))|~r1_tsep_1(X31,X32)|(v2_struct_0(X32)|~m1_pre_topc(X32,X29))|(v2_struct_0(X31)|~m1_pre_topc(X31,X29))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))))&(m1_subset_1(k10_tmap_1(X29,X30,X31,X32,X33,X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X31,X32)),u1_struct_0(X30))))|~r4_tsep_1(X29,X31,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X30))|~v5_pre_topc(X34,X32,X30)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30)))))|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))|~v5_pre_topc(X33,X31,X30)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30)))))|~r1_tsep_1(X31,X32)|(v2_struct_0(X32)|~m1_pre_topc(X32,X29))|(v2_struct_0(X31)|~m1_pre_topc(X31,X29))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_46]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_68, plain, (l1_pre_topc(esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61]), c_0_62])).
% 0.19/0.40  cnf(c_0_70, plain, (v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~v5_pre_topc(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~r1_tsep_1(X3,X4)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (v5_pre_topc(esk7_0,esk4_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (v5_pre_topc(esk8_0,esk5_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_74, plain, (v2_pre_topc(esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (~r4_tsep_1(esk3_0,esk4_0,esk5_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61]), c_0_71]), c_0_72]), c_0_62])).
% 0.19/0.40  cnf(c_0_76, plain, (v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  fof(c_0_77, plain, ![X35, X36, X37]:((~r1_tsep_1(X36,X37)|~r4_tsep_1(X35,X36,X37)|r3_tsep_1(X35,X36,X37)|(v2_struct_0(X37)|~m1_pre_topc(X37,X35))|(v2_struct_0(X36)|~m1_pre_topc(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&((r1_tsep_1(X36,X37)|~r3_tsep_1(X35,X36,X37)|(v2_struct_0(X37)|~m1_pre_topc(X37,X35))|(v2_struct_0(X36)|~m1_pre_topc(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(r4_tsep_1(X35,X36,X37)|~r3_tsep_1(X35,X36,X37)|(v2_struct_0(X37)|~m1_pre_topc(X37,X35))|(v2_struct_0(X36)|~m1_pre_topc(X36,X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t85_tsep_1])])])])])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (~r4_tsep_1(esk3_0,esk4_0,esk5_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61]), c_0_62])).
% 0.19/0.40  cnf(c_0_80, plain, (r4_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_tsep_1(X1,X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.40  cnf(c_0_81, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk1_3(X1,X2,X3))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_45]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22]), c_0_23]), c_0_29])).
% 0.19/0.40  cnf(c_0_85, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~r3_tsep_1(X3,X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (~r1_tsep_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_84]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_23]), c_0_21]), c_0_22]), c_0_86]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 88
% 0.19/0.40  # Proof object clause steps            : 73
% 0.19/0.40  # Proof object formula steps           : 15
% 0.19/0.40  # Proof object conjectures             : 52
% 0.19/0.40  # Proof object clause conjectures      : 49
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 47
% 0.19/0.40  # Proof object initial formulas used   : 7
% 0.19/0.40  # Proof object generating inferences   : 24
% 0.19/0.40  # Proof object simplifying inferences  : 237
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 7
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 57
% 0.19/0.40  # Removed in clause preprocessing      : 3
% 0.19/0.40  # Initial clauses in saturation        : 54
% 0.19/0.40  # Processed clauses                    : 137
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 6
% 0.19/0.40  # ...remaining for further processing  : 130
% 0.19/0.40  # Other redundant clauses eliminated   : 1
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 32
% 0.19/0.40  # Backward-rewritten                   : 10
% 0.19/0.40  # Generated clauses                    : 50
% 0.19/0.40  # ...of the previous two non-trivial   : 37
% 0.19/0.40  # Contextual simplify-reflections      : 67
% 0.19/0.40  # Paramodulations                      : 49
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 1
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 37
% 0.19/0.40  #    Positive orientable unit clauses  : 5
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 4
% 0.19/0.40  #    Non-unit-clauses                  : 28
% 0.19/0.40  # Current number of unprocessed clauses: 4
% 0.19/0.40  # ...number of literals in the above   : 72
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 92
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 6226
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 270
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 105
% 0.19/0.40  # Unit Clause-clause subsumption calls : 7
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 1
% 0.19/0.40  # BW rewrite match successes           : 1
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 17409
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.058 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.064 s
% 0.19/0.40  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------

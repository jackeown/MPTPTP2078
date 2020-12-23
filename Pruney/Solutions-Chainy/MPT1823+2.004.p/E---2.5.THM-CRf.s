%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:34 EST 2020

% Result     : Theorem 9.02s
% Output     : CNFRefutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :  104 (1355 expanded)
%              Number of clauses        :   79 ( 469 expanded)
%              Number of leaves         :   12 ( 330 expanded)
%              Depth                    :   17
%              Number of atoms          :  599 (12447 expanded)
%              Number of equality atoms :   28 ( 714 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   51 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t139_tmap_1,conjecture,(
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
                 => ( X1 = k1_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3),k2_tmap_1(X1,X2,X5,X4))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

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

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_12,negated_conjecture,(
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
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( X1 = k1_tsep_1(X1,X3,X4)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                         => r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3),k2_tmap_1(X1,X2,X5,X4))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t139_tmap_1])).

fof(c_0_13,plain,(
    ! [X36,X37,X38,X39] :
      ( ( v1_funct_1(k2_tmap_1(X36,X37,X38,X39))
        | ~ l1_struct_0(X36)
        | ~ l1_struct_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ l1_struct_0(X39) )
      & ( v1_funct_2(k2_tmap_1(X36,X37,X38,X39),u1_struct_0(X39),u1_struct_0(X37))
        | ~ l1_struct_0(X36)
        | ~ l1_struct_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ l1_struct_0(X39) )
      & ( m1_subset_1(k2_tmap_1(X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37))))
        | ~ l1_struct_0(X36)
        | ~ l1_struct_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ l1_struct_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & esk1_0 = k1_tsep_1(esk1_0,esk3_0,esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_20,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_23,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | l1_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_24])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_28])])).

cnf(c_0_33,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_28])])).

fof(c_0_37,plain,(
    ! [X21,X22,X23,X24] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
      | ~ m1_pre_topc(X24,X21)
      | k2_tmap_1(X21,X22,X23,X24) = k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_38,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( v1_funct_1(k10_tmap_1(X30,X31,X32,X33,X34,X35))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X31))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31)))) )
      & ( v1_funct_2(k10_tmap_1(X30,X31,X32,X33,X34,X35),u1_struct_0(k1_tsep_1(X30,X32,X33)),u1_struct_0(X31))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X31))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31)))) )
      & ( m1_subset_1(k10_tmap_1(X30,X31,X32,X33,X34,X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X30,X32,X33)),u1_struct_0(X31))))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X31))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_44,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X25)
      | ~ m1_pre_topc(X28,X25)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))
      | ~ m1_pre_topc(X28,X27)
      | k3_tmap_1(X25,X26,X27,X28,X29) = k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),X29,u1_struct_0(X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_43]),c_0_28])])).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_16]),c_0_46]),c_0_47]),c_0_24]),c_0_28]),c_0_17]),c_0_18])]),c_0_48]),c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_46]),c_0_24]),c_0_52]),c_0_53])]),c_0_54]),c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_46]),c_0_24]),c_0_52]),c_0_53])]),c_0_54]),c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_46]),c_0_24]),c_0_52]),c_0_53])]),c_0_54]),c_0_48])).

fof(c_0_67,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | v2_struct_0(X42)
      | ~ m1_pre_topc(X42,X40)
      | v2_struct_0(X43)
      | ~ m1_pre_topc(X43,X40)
      | ~ v1_funct_1(X44)
      | ~ v1_funct_2(X44,u1_struct_0(k1_tsep_1(X40,X42,X43)),u1_struct_0(X41))
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X42,X43)),u1_struct_0(X41))))
      | r2_funct_2(u1_struct_0(k1_tsep_1(X40,X42,X43)),u1_struct_0(X41),X44,k10_tmap_1(X40,X41,X42,X43,k3_tmap_1(X40,X41,k1_tsep_1(X40,X42,X43),X42,X44),k3_tmap_1(X40,X41,k1_tsep_1(X40,X42,X43),X43,X44))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t138_tmap_1])])])])).

cnf(c_0_68,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_16]),c_0_46]),c_0_24]),c_0_17]),c_0_18])]),c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_43])).

fof(c_0_70,plain,(
    ! [X45] :
      ( ~ l1_pre_topc(X45)
      | m1_pre_topc(X45,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_71,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_34])).

fof(c_0_72,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r1_funct_2(X15,X16,X17,X18,X19,X20)
        | X19 = X20
        | v1_xboole_0(X16)
        | v1_xboole_0(X18)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X15,X16)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X19 != X20
        | r1_funct_2(X15,X16,X17,X18,X19,X20)
        | v1_xboole_0(X16)
        | v1_xboole_0(X18)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X15,X16)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

fof(c_0_73,plain,(
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

cnf(c_0_74,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])]),c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_61]),c_0_62]),c_0_63])]),c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_61]),c_0_62]),c_0_63])]),c_0_64])).

cnf(c_0_78,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_69])).

cnf(c_0_80,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_34]),c_0_71])).

cnf(c_0_82,plain,
    ( r1_funct_2(X3,X4,X5,X6,X1,X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X6)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_83,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_34]),c_0_75]),c_0_47]),c_0_43]),c_0_28])]),c_0_49])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_34]),c_0_75]),c_0_47]),c_0_43]),c_0_28])]),c_0_49])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_34]),c_0_47]),c_0_43]),c_0_28])]),c_0_49])).

cnf(c_0_87,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(X1),X2,k10_tmap_1(esk1_0,X1,esk3_0,esk4_0,k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_75]),c_0_47]),c_0_34]),c_0_43]),c_0_28])]),c_0_54]),c_0_64]),c_0_49])).

cnf(c_0_88,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_47]),c_0_43]),c_0_28])]),c_0_49])).

cnf(c_0_89,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_80]),c_0_47]),c_0_34]),c_0_28])]),c_0_49])).

cnf(c_0_90,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_92,negated_conjecture,
    ( X1 = k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_86])])).

cnf(c_0_93,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_16]),c_0_88]),c_0_89]),c_0_46]),c_0_24]),c_0_17]),c_0_18])]),c_0_48])).

cnf(c_0_94,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(esk5_0,X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_91,c_0_75])).

cnf(c_0_96,negated_conjecture,
    ( k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_16]),c_0_17]),c_0_18])])).

fof(c_0_97,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_98,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_16]),c_0_17])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_102,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_48])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 9.02/9.23  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S059I
% 9.02/9.23  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 9.02/9.23  #
% 9.02/9.23  # Preprocessing time       : 0.029 s
% 9.02/9.23  # Presaturation interreduction done
% 9.02/9.23  
% 9.02/9.23  # Proof found!
% 9.02/9.23  # SZS status Theorem
% 9.02/9.23  # SZS output start CNFRefutation
% 9.02/9.23  fof(t139_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(X1=k1_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3),k2_tmap_1(X1,X2,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_tmap_1)).
% 9.02/9.23  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 9.02/9.23  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.02/9.23  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.02/9.23  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.02/9.23  fof(dt_k10_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(X6))&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 9.02/9.23  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 9.02/9.23  fof(t138_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_tmap_1)).
% 9.02/9.23  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.02/9.23  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 9.02/9.23  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 9.02/9.23  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 9.02/9.23  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(X1=k1_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3),k2_tmap_1(X1,X2,X5,X4)))))))))), inference(assume_negation,[status(cth)],[t139_tmap_1])).
% 9.02/9.23  fof(c_0_13, plain, ![X36, X37, X38, X39]:(((v1_funct_1(k2_tmap_1(X36,X37,X38,X39))|(~l1_struct_0(X36)|~l1_struct_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|~l1_struct_0(X39)))&(v1_funct_2(k2_tmap_1(X36,X37,X38,X39),u1_struct_0(X39),u1_struct_0(X37))|(~l1_struct_0(X36)|~l1_struct_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|~l1_struct_0(X39))))&(m1_subset_1(k2_tmap_1(X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37))))|(~l1_struct_0(X36)|~l1_struct_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|~l1_struct_0(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 9.02/9.23  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(esk1_0=k1_tsep_1(esk1_0,esk3_0,esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 9.02/9.23  cnf(c_0_15, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 9.02/9.23  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  fof(c_0_19, plain, ![X11]:(~l1_pre_topc(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 9.02/9.23  cnf(c_0_20, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 9.02/9.23  cnf(c_0_21, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 9.02/9.23  cnf(c_0_22, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 9.02/9.23  cnf(c_0_23, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 9.02/9.23  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_25, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_17]), c_0_18])])).
% 9.02/9.23  cnf(c_0_26, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_17]), c_0_18])])).
% 9.02/9.23  cnf(c_0_27, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 9.02/9.23  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  fof(c_0_29, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|l1_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 9.02/9.23  cnf(c_0_30, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_24])])).
% 9.02/9.23  cnf(c_0_31, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_23]), c_0_24])])).
% 9.02/9.23  cnf(c_0_32, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_23]), c_0_28])])).
% 9.02/9.23  cnf(c_0_33, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 9.02/9.23  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_35, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_23]), c_0_28])])).
% 9.02/9.23  cnf(c_0_36, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_23]), c_0_28])])).
% 9.02/9.23  fof(c_0_37, plain, ![X21, X22, X23, X24]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|(~m1_pre_topc(X24,X21)|k2_tmap_1(X21,X22,X23,X24)=k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 9.02/9.23  fof(c_0_38, plain, ![X30, X31, X32, X33, X34, X35]:(((v1_funct_1(k10_tmap_1(X30,X31,X32,X33,X34,X35))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)|v2_struct_0(X33)|~m1_pre_topc(X33,X30)|~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))|~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X31))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))))&(v1_funct_2(k10_tmap_1(X30,X31,X32,X33,X34,X35),u1_struct_0(k1_tsep_1(X30,X32,X33)),u1_struct_0(X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)|v2_struct_0(X33)|~m1_pre_topc(X33,X30)|~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))|~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X31))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31)))))))&(m1_subset_1(k10_tmap_1(X30,X31,X32,X33,X34,X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X30,X32,X33)),u1_struct_0(X31))))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)|v2_struct_0(X33)|~m1_pre_topc(X33,X30)|~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))|~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X31))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).
% 9.02/9.23  cnf(c_0_39, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_32, c_0_23])).
% 9.02/9.23  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28])])).
% 9.02/9.23  cnf(c_0_41, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_23])).
% 9.02/9.23  cnf(c_0_42, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_23])).
% 9.02/9.23  cnf(c_0_43, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  fof(c_0_44, plain, ![X25, X26, X27, X28, X29]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(~m1_pre_topc(X27,X25)|(~m1_pre_topc(X28,X25)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))|(~m1_pre_topc(X28,X27)|k3_tmap_1(X25,X26,X27,X28,X29)=k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),X29,u1_struct_0(X28)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 9.02/9.23  cnf(c_0_45, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 9.02/9.23  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_47, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_48, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_50, plain, (m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 9.02/9.23  cnf(c_0_51, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 9.02/9.23  cnf(c_0_52, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 9.02/9.23  cnf(c_0_53, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 9.02/9.23  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_43]), c_0_28])])).
% 9.02/9.23  cnf(c_0_56, plain, (v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 9.02/9.23  cnf(c_0_57, plain, (v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 9.02/9.23  cnf(c_0_58, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 9.02/9.23  cnf(c_0_59, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_16]), c_0_46]), c_0_47]), c_0_24]), c_0_28]), c_0_17]), c_0_18])]), c_0_48]), c_0_49])).
% 9.02/9.23  cnf(c_0_60, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_46]), c_0_24]), c_0_52]), c_0_53])]), c_0_54]), c_0_48])).
% 9.02/9.23  cnf(c_0_61, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_39, c_0_55])).
% 9.02/9.23  cnf(c_0_62, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_55])).
% 9.02/9.23  cnf(c_0_63, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_55])).
% 9.02/9.23  cnf(c_0_64, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_65, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_51]), c_0_46]), c_0_24]), c_0_52]), c_0_53])]), c_0_54]), c_0_48])).
% 9.02/9.23  cnf(c_0_66, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_51]), c_0_46]), c_0_24]), c_0_52]), c_0_53])]), c_0_54]), c_0_48])).
% 9.02/9.23  fof(c_0_67, plain, ![X40, X41, X42, X43, X44]:(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(v2_struct_0(X42)|~m1_pre_topc(X42,X40)|(v2_struct_0(X43)|~m1_pre_topc(X43,X40)|(~v1_funct_1(X44)|~v1_funct_2(X44,u1_struct_0(k1_tsep_1(X40,X42,X43)),u1_struct_0(X41))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X42,X43)),u1_struct_0(X41))))|r2_funct_2(u1_struct_0(k1_tsep_1(X40,X42,X43)),u1_struct_0(X41),X44,k10_tmap_1(X40,X41,X42,X43,k3_tmap_1(X40,X41,k1_tsep_1(X40,X42,X43),X42,X44),k3_tmap_1(X40,X41,k1_tsep_1(X40,X42,X43),X43,X44)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t138_tmap_1])])])])).
% 9.02/9.23  cnf(c_0_68, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_16]), c_0_46]), c_0_24]), c_0_17]), c_0_18])]), c_0_48])).
% 9.02/9.23  cnf(c_0_69, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_59, c_0_43])).
% 9.02/9.23  fof(c_0_70, plain, ![X45]:(~l1_pre_topc(X45)|m1_pre_topc(X45,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 9.02/9.23  cnf(c_0_71, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_34])).
% 9.02/9.23  fof(c_0_72, plain, ![X15, X16, X17, X18, X19, X20]:((~r1_funct_2(X15,X16,X17,X18,X19,X20)|X19=X20|(v1_xboole_0(X16)|v1_xboole_0(X18)|~v1_funct_1(X19)|~v1_funct_2(X19,X15,X16)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|~v1_funct_1(X20)|~v1_funct_2(X20,X17,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(X19!=X20|r1_funct_2(X15,X16,X17,X18,X19,X20)|(v1_xboole_0(X16)|v1_xboole_0(X18)|~v1_funct_1(X19)|~v1_funct_2(X19,X15,X16)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|~v1_funct_1(X20)|~v1_funct_2(X20,X17,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 9.02/9.23  fof(c_0_73, plain, ![X7, X8, X9, X10]:((~r2_funct_2(X7,X8,X9,X10)|X9=X10|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(X9!=X10|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 9.02/9.23  cnf(c_0_74, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63])]), c_0_64])).
% 9.02/9.23  cnf(c_0_75, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_76, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_61]), c_0_62]), c_0_63])]), c_0_64])).
% 9.02/9.23  cnf(c_0_77, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_61]), c_0_62]), c_0_63])]), c_0_64])).
% 9.02/9.23  cnf(c_0_78, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 9.02/9.23  cnf(c_0_79, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_43]), c_0_69])).
% 9.02/9.23  cnf(c_0_80, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 9.02/9.23  cnf(c_0_81, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_34]), c_0_71])).
% 9.02/9.23  cnf(c_0_82, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 9.02/9.23  cnf(c_0_83, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 9.02/9.23  cnf(c_0_84, negated_conjecture, (m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_34]), c_0_75]), c_0_47]), c_0_43]), c_0_28])]), c_0_49])).
% 9.02/9.23  cnf(c_0_85, negated_conjecture, (v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_34]), c_0_75]), c_0_47]), c_0_43]), c_0_28])]), c_0_49])).
% 9.02/9.23  cnf(c_0_86, negated_conjecture, (v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_34]), c_0_47]), c_0_43]), c_0_28])]), c_0_49])).
% 9.02/9.23  cnf(c_0_87, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(X1),X2,k10_tmap_1(esk1_0,X1,esk3_0,esk4_0,k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_75]), c_0_47]), c_0_34]), c_0_43]), c_0_28])]), c_0_54]), c_0_64]), c_0_49])).
% 9.02/9.23  cnf(c_0_88, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_47]), c_0_43]), c_0_28])]), c_0_49])).
% 9.02/9.23  cnf(c_0_89, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_80]), c_0_47]), c_0_34]), c_0_28])]), c_0_49])).
% 9.02/9.23  cnf(c_0_90, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)), inference(er,[status(thm)],[c_0_82])).
% 9.02/9.23  cnf(c_0_91, negated_conjecture, (~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.02/9.23  cnf(c_0_92, negated_conjecture, (X1=k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_86])])).
% 9.02/9.23  cnf(c_0_93, negated_conjecture, (r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_16]), c_0_88]), c_0_89]), c_0_46]), c_0_24]), c_0_17]), c_0_18])]), c_0_48])).
% 9.02/9.23  cnf(c_0_94, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(esk5_0,X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_16]), c_0_17]), c_0_18])])).
% 9.02/9.23  cnf(c_0_95, negated_conjecture, (~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))), inference(rw,[status(thm)],[c_0_91, c_0_75])).
% 9.02/9.23  cnf(c_0_96, negated_conjecture, (k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_16]), c_0_17]), c_0_18])])).
% 9.02/9.23  fof(c_0_97, plain, ![X14]:(v2_struct_0(X14)|~l1_struct_0(X14)|~v1_xboole_0(u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 9.02/9.24  cnf(c_0_98, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_16]), c_0_17])])).
% 9.02/9.24  cnf(c_0_99, negated_conjecture, (~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 9.02/9.24  cnf(c_0_100, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 9.02/9.24  cnf(c_0_101, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_98, c_0_99])).
% 9.02/9.24  cnf(c_0_102, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_48])).
% 9.02/9.24  cnf(c_0_103, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_23]), c_0_24])]), ['proof']).
% 9.02/9.24  # SZS output end CNFRefutation
% 9.02/9.24  # Proof object total steps             : 104
% 9.02/9.24  # Proof object clause steps            : 79
% 9.02/9.24  # Proof object formula steps           : 25
% 9.02/9.24  # Proof object conjectures             : 66
% 9.02/9.24  # Proof object clause conjectures      : 63
% 9.02/9.24  # Proof object formula conjectures     : 3
% 9.02/9.24  # Proof object initial clauses used    : 30
% 9.02/9.24  # Proof object initial formulas used   : 12
% 9.02/9.24  # Proof object generating inferences   : 45
% 9.02/9.24  # Proof object simplifying inferences  : 137
% 9.02/9.24  # Training examples: 0 positive, 0 negative
% 9.02/9.24  # Parsed axioms                        : 12
% 9.02/9.24  # Removed by relevancy pruning/SinE    : 0
% 9.02/9.24  # Initial clauses                      : 32
% 9.02/9.24  # Removed in clause preprocessing      : 0
% 9.02/9.24  # Initial clauses in saturation        : 32
% 9.02/9.24  # Processed clauses                    : 17821
% 9.02/9.24  # ...of these trivial                  : 0
% 9.02/9.24  # ...subsumed                          : 4
% 9.02/9.24  # ...remaining for further processing  : 17817
% 9.02/9.24  # Other redundant clauses eliminated   : 2
% 9.02/9.24  # Clauses deleted for lack of memory   : 0
% 9.02/9.24  # Backward-subsumed                    : 1306
% 9.02/9.24  # Backward-rewritten                   : 951
% 9.02/9.24  # Generated clauses                    : 114707
% 9.02/9.24  # ...of the previous two non-trivial   : 114844
% 9.02/9.24  # Contextual simplify-reflections      : 4
% 9.02/9.24  # Paramodulations                      : 114704
% 9.02/9.24  # Factorizations                       : 0
% 9.02/9.24  # Equation resolutions                 : 2
% 9.02/9.24  # Propositional unsat checks           : 3
% 9.02/9.24  #    Propositional check models        : 3
% 9.02/9.24  #    Propositional check unsatisfiable : 0
% 9.02/9.24  #    Propositional clauses             : 0
% 9.02/9.24  #    Propositional clauses after purity: 0
% 9.02/9.24  #    Propositional unsat core size     : 0
% 9.02/9.24  #    Propositional preprocessing time  : 0.000
% 9.02/9.24  #    Propositional encoding time       : 0.189
% 9.02/9.24  #    Propositional solver time         : 0.018
% 9.02/9.24  #    Success case prop preproc time    : 0.000
% 9.02/9.24  #    Success case prop encoding time   : 0.000
% 9.02/9.24  #    Success case prop solver time     : 0.000
% 9.02/9.24  # Current number of processed clauses  : 15525
% 9.02/9.24  #    Positive orientable unit clauses  : 5141
% 9.02/9.24  #    Positive unorientable unit clauses: 0
% 9.02/9.24  #    Negative unit clauses             : 6
% 9.02/9.24  #    Non-unit-clauses                  : 10378
% 9.02/9.24  # Current number of unprocessed clauses: 97087
% 9.02/9.24  # ...number of literals in the above   : 627474
% 9.02/9.24  # Current number of archived formulas  : 0
% 9.02/9.24  # Current number of archived clauses   : 2290
% 9.02/9.24  # Clause-clause subsumption calls (NU) : 22577568
% 9.02/9.24  # Rec. Clause-clause subsumption calls : 2290206
% 9.02/9.24  # Non-unit clause-clause subsumptions  : 1314
% 9.02/9.24  # Unit Clause-clause subsumption calls : 11050181
% 9.02/9.24  # Rewrite failures with RHS unbound    : 0
% 9.02/9.24  # BW rewrite match attempts            : 2870876
% 9.02/9.24  # BW rewrite match successes           : 435
% 9.02/9.24  # Condensation attempts                : 0
% 9.02/9.24  # Condensation successes               : 0
% 9.02/9.24  # Termbank termtop insertions          : 13108830
% 9.02/9.25  
% 9.02/9.25  # -------------------------------------------------
% 9.02/9.25  # User time                : 8.787 s
% 9.02/9.25  # System time              : 0.120 s
% 9.02/9.25  # Total time               : 8.908 s
% 9.02/9.25  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------

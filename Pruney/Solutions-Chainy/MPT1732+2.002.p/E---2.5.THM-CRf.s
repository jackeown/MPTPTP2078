%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:11 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   72 (1256 expanded)
%              Number of clauses        :   55 ( 430 expanded)
%              Number of leaves         :    8 ( 305 expanded)
%              Depth                    :   26
%              Number of atoms          :  411 (13998 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   60 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_tmap_1,conjecture,(
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
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ( ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
                       => ( ~ r1_tsep_1(X2,X4)
                          & ~ r1_tsep_1(X3,X4) ) )
                      & ( ~ r1_tsep_1(X4,k2_tsep_1(X1,X2,X3))
                       => ( ~ r1_tsep_1(X4,X2)
                          & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tmap_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t35_tmap_1,axiom,(
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
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X4,X5) )
                       => ( ( ~ r1_tsep_1(X3,X5)
                            & ~ r1_tsep_1(k2_tsep_1(X1,X3,X5),k1_tsep_1(X1,X2,X4)) )
                          | ( r1_tsep_1(X3,X4)
                            & r1_tsep_1(X5,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t30_tsep_1,axiom,(
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
             => ( ~ r1_tsep_1(X2,X3)
               => ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
                  & m1_pre_topc(k2_tsep_1(X1,X2,X3),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

fof(dt_k2_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
        & v1_pre_topc(k2_tsep_1(X1,X2,X3))
        & m1_pre_topc(k2_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(c_0_8,negated_conjecture,(
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
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( ~ r1_tsep_1(X2,X3)
                     => ( ( ~ r1_tsep_1(k2_tsep_1(X1,X2,X3),X4)
                         => ( ~ r1_tsep_1(X2,X4)
                            & ~ r1_tsep_1(X3,X4) ) )
                        & ( ~ r1_tsep_1(X4,k2_tsep_1(X1,X2,X3))
                         => ( ~ r1_tsep_1(X4,X2)
                            & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_tmap_1])).

fof(c_0_9,plain,(
    ! [X12,X13] :
      ( ~ l1_struct_0(X12)
      | ~ l1_struct_0(X13)
      | ~ r1_tsep_1(X12,X13)
      | r1_tsep_1(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ r1_tsep_1(esk2_0,esk3_0)
    & ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
      | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,esk3_0)
      | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) )
    & ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(esk3_0,esk4_0) )
    & ( r1_tsep_1(esk4_0,esk2_0)
      | r1_tsep_1(esk4_0,esk3_0)
      | r1_tsep_1(esk2_0,esk4_0)
      | r1_tsep_1(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | l1_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_12,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_15,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_21]),c_0_17])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk2_0,esk4_0)
    | r1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_23])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_27,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( r1_tsep_1(X20,X21)
        | ~ r1_tsep_1(X20,X22)
        | ~ m1_pre_topc(X19,X20)
        | ~ m1_pre_topc(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X18)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r1_tsep_1(X22,X19)
        | ~ r1_tsep_1(X20,X22)
        | ~ m1_pre_topc(X19,X20)
        | ~ m1_pre_topc(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X18)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r1_tsep_1(X20,X21)
        | ~ r1_tsep_1(k2_tsep_1(X18,X20,X22),k1_tsep_1(X18,X19,X21))
        | ~ m1_pre_topc(X19,X20)
        | ~ m1_pre_topc(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X18)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r1_tsep_1(X22,X19)
        | ~ r1_tsep_1(k2_tsep_1(X18,X20,X22),k1_tsep_1(X18,X19,X21))
        | ~ m1_pre_topc(X19,X20)
        | ~ m1_pre_topc(X21,X22)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X18)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_tmap_1])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_20])])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_26]),c_0_17])])).

fof(c_0_30,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | m1_pre_topc(X14,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_31,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ r1_tsep_1(X1,X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X3,X5)
    | ~ m1_pre_topc(X2,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | r1_tsep_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X15,X16,X17] :
      ( ( m1_pre_topc(k2_tsep_1(X15,X16,X17),X16)
        | r1_tsep_1(X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_pre_topc(k2_tsep_1(X15,X16,X17),X17)
        | r1_tsep_1(X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).

fof(c_0_37,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_struct_0(k2_tsep_1(X9,X10,X11))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) )
      & ( v1_pre_topc(k2_tsep_1(X9,X10,X11))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) )
      & ( m1_pre_topc(k2_tsep_1(X9,X10,X11),X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk3_0,X3)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk4_0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_40,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_41]),c_0_17])]),c_0_33]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_17])]),c_0_33]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | r1_tsep_1(esk4_0,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_41]),c_0_16]),c_0_17])]),c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_46]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_26]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_19]),c_0_20])])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_51]),c_0_17])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_19]),c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk2_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk2_0,X3)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(esk4_0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_58]),c_0_47]),c_0_34])).

cnf(c_0_60,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_39]),c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_21]),c_0_41]),c_0_17])]),c_0_33]),c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( r1_tsep_1(esk4_0,X1)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_26]),c_0_41]),c_0_16]),c_0_17])]),c_0_42])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_26]),c_0_46]),c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_51])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | ~ l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_19]),c_0_20])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_19]),c_0_55])])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_68]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_21]),c_0_26]),c_0_17])]),c_0_33]),c_0_47]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.92/1.13  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04CA
% 0.92/1.13  # and selection function MSelectComplexExceptUniqMaxHorn.
% 0.92/1.13  #
% 0.92/1.13  # Preprocessing time       : 0.028 s
% 0.92/1.13  # Presaturation interreduction done
% 0.92/1.13  
% 0.92/1.13  # Proof found!
% 0.92/1.13  # SZS status Theorem
% 0.92/1.13  # SZS output start CNFRefutation
% 0.92/1.13  fof(t41_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((~(r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))=>(~(r1_tsep_1(X2,X4))&~(r1_tsep_1(X3,X4))))&(~(r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)))=>(~(r1_tsep_1(X4,X2))&~(r1_tsep_1(X4,X3)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tmap_1)).
% 0.92/1.13  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.92/1.13  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.92/1.13  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.92/1.13  fof(t35_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X2,X3)&m1_pre_topc(X4,X5))=>((~(r1_tsep_1(X3,X5))&~(r1_tsep_1(k2_tsep_1(X1,X3,X5),k1_tsep_1(X1,X2,X4))))|(r1_tsep_1(X3,X4)&r1_tsep_1(X5,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tmap_1)).
% 0.92/1.13  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.92/1.13  fof(t30_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>(m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)&m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tsep_1)).
% 0.92/1.13  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.92/1.13  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(~(r1_tsep_1(X2,X3))=>((~(r1_tsep_1(k2_tsep_1(X1,X2,X3),X4))=>(~(r1_tsep_1(X2,X4))&~(r1_tsep_1(X3,X4))))&(~(r1_tsep_1(X4,k2_tsep_1(X1,X2,X3)))=>(~(r1_tsep_1(X4,X2))&~(r1_tsep_1(X4,X3))))))))))), inference(assume_negation,[status(cth)],[t41_tmap_1])).
% 0.92/1.13  fof(c_0_9, plain, ![X12, X13]:(~l1_struct_0(X12)|~l1_struct_0(X13)|(~r1_tsep_1(X12,X13)|r1_tsep_1(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.92/1.13  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(~r1_tsep_1(esk2_0,esk3_0)&(((~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0))&(r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)))&((~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)))&(r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|(r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.92/1.13  fof(c_0_11, plain, ![X7, X8]:(~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|l1_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.92/1.13  cnf(c_0_12, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.92/1.13  cnf(c_0_13, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  fof(c_0_14, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.92/1.13  cnf(c_0_15, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.92/1.13  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_18, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.92/1.13  cnf(c_0_19, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.92/1.13  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.92/1.13  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_22, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk2_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.92/1.13  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_21]), c_0_17])])).
% 0.92/1.13  cnf(c_0_24, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk2_0,esk4_0)|r1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_23])])).
% 0.92/1.13  cnf(c_0_25, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_24])).
% 0.92/1.13  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  fof(c_0_27, plain, ![X18, X19, X20, X21, X22]:(((r1_tsep_1(X20,X21)|~r1_tsep_1(X20,X22)|(~m1_pre_topc(X19,X20)|~m1_pre_topc(X21,X22))|(v2_struct_0(X22)|~m1_pre_topc(X22,X18))|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(r1_tsep_1(X22,X19)|~r1_tsep_1(X20,X22)|(~m1_pre_topc(X19,X20)|~m1_pre_topc(X21,X22))|(v2_struct_0(X22)|~m1_pre_topc(X22,X18))|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))))&((r1_tsep_1(X20,X21)|~r1_tsep_1(k2_tsep_1(X18,X20,X22),k1_tsep_1(X18,X19,X21))|(~m1_pre_topc(X19,X20)|~m1_pre_topc(X21,X22))|(v2_struct_0(X22)|~m1_pre_topc(X22,X18))|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(r1_tsep_1(X22,X19)|~r1_tsep_1(k2_tsep_1(X18,X20,X22),k1_tsep_1(X18,X19,X21))|(~m1_pre_topc(X19,X20)|~m1_pre_topc(X21,X22))|(v2_struct_0(X22)|~m1_pre_topc(X22,X18))|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_tmap_1])])])])])).
% 0.92/1.13  cnf(c_0_28, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,esk3_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_20])])).
% 0.92/1.13  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_26]), c_0_17])])).
% 0.92/1.13  fof(c_0_30, plain, ![X14]:(~l1_pre_topc(X14)|m1_pre_topc(X14,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.92/1.13  cnf(c_0_31, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X5)|~r1_tsep_1(X1,X3)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X3,X5)|~m1_pre_topc(X2,X5)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X4,X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.92/1.13  cnf(c_0_32, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|r1_tsep_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_19]), c_0_29])])).
% 0.92/1.13  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_35, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.92/1.13  fof(c_0_36, plain, ![X15, X16, X17]:((m1_pre_topc(k2_tsep_1(X15,X16,X17),X16)|r1_tsep_1(X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(m1_pre_topc(k2_tsep_1(X15,X16,X17),X17)|r1_tsep_1(X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_tsep_1])])])])])).
% 0.92/1.13  fof(c_0_37, plain, ![X9, X10, X11]:(((~v2_struct_0(k2_tsep_1(X9,X10,X11))|(v2_struct_0(X9)|~l1_pre_topc(X9)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|v2_struct_0(X11)|~m1_pre_topc(X11,X9)))&(v1_pre_topc(k2_tsep_1(X9,X10,X11))|(v2_struct_0(X9)|~l1_pre_topc(X9)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|v2_struct_0(X11)|~m1_pre_topc(X11,X9))))&(m1_pre_topc(k2_tsep_1(X9,X10,X11),X9)|(v2_struct_0(X9)|~l1_pre_topc(X9)|v2_struct_0(X10)|~m1_pre_topc(X10,X9)|v2_struct_0(X11)|~m1_pre_topc(X11,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.92/1.13  cnf(c_0_38, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_pre_topc(X3)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk3_0,X3)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(esk4_0,X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.92/1.13  cnf(c_0_39, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_20])).
% 0.92/1.13  cnf(c_0_40, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X3)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.92/1.13  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_43, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.92/1.13  cnf(c_0_44, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X2)|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_34])).
% 0.92/1.13  cnf(c_0_45, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_41]), c_0_17])]), c_0_33]), c_0_42])).
% 0.92/1.13  cnf(c_0_46, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_48, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_17])]), c_0_33]), c_0_42])).
% 0.92/1.13  cnf(c_0_49, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|r1_tsep_1(esk4_0,X1)|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_41]), c_0_16]), c_0_17])]), c_0_42])).
% 0.92/1.13  cnf(c_0_50, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_46]), c_0_47])).
% 0.92/1.13  cnf(c_0_51, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_26]), c_0_47])).
% 0.92/1.13  cnf(c_0_52, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.92/1.13  cnf(c_0_53, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_52])).
% 0.92/1.13  cnf(c_0_54, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_19]), c_0_20])])).
% 0.92/1.13  cnf(c_0_55, negated_conjecture, (l1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_51]), c_0_17])])).
% 0.92/1.13  cnf(c_0_56, negated_conjecture, (~r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|~r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.92/1.13  cnf(c_0_57, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_19]), c_0_55])])).
% 0.92/1.13  cnf(c_0_58, negated_conjecture, (r1_tsep_1(esk4_0,esk2_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_52])).
% 0.92/1.13  cnf(c_0_59, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_pre_topc(X3)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk2_0,X3)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(esk4_0,X3)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_58]), c_0_47]), c_0_34])).
% 0.92/1.13  cnf(c_0_60, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X2)|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.92/1.13  cnf(c_0_61, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X2)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_39]), c_0_34])).
% 0.92/1.13  cnf(c_0_62, negated_conjecture, (r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_21]), c_0_41]), c_0_17])]), c_0_33]), c_0_42])).
% 0.92/1.13  cnf(c_0_63, negated_conjecture, (r1_tsep_1(esk4_0,X1)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_26]), c_0_41]), c_0_16]), c_0_17])]), c_0_42])).
% 0.92/1.13  cnf(c_0_64, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_26]), c_0_46]), c_0_47])).
% 0.92/1.13  cnf(c_0_65, negated_conjecture, (r1_tsep_1(esk4_0,k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_51])])).
% 0.92/1.13  cnf(c_0_66, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_65])).
% 0.92/1.13  cnf(c_0_67, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|~l1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_19]), c_0_20])])).
% 0.92/1.13  cnf(c_0_68, negated_conjecture, (r1_tsep_1(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)|v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_19]), c_0_55])])).
% 0.92/1.13  cnf(c_0_69, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.92/1.13  cnf(c_0_70, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_68]), c_0_65])).
% 0.92/1.13  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_21]), c_0_26]), c_0_17])]), c_0_33]), c_0_47]), c_0_42]), ['proof']).
% 0.92/1.13  # SZS output end CNFRefutation
% 0.92/1.13  # Proof object total steps             : 72
% 0.92/1.13  # Proof object clause steps            : 55
% 0.92/1.13  # Proof object formula steps           : 17
% 0.92/1.13  # Proof object conjectures             : 49
% 0.92/1.13  # Proof object clause conjectures      : 46
% 0.92/1.13  # Proof object formula conjectures     : 3
% 0.92/1.13  # Proof object initial clauses used    : 21
% 0.92/1.13  # Proof object initial formulas used   : 8
% 0.92/1.13  # Proof object generating inferences   : 34
% 0.92/1.13  # Proof object simplifying inferences  : 72
% 0.92/1.13  # Training examples: 0 positive, 0 negative
% 0.92/1.13  # Parsed axioms                        : 8
% 0.92/1.13  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.13  # Initial clauses                      : 27
% 0.92/1.13  # Removed in clause preprocessing      : 0
% 0.92/1.13  # Initial clauses in saturation        : 27
% 0.92/1.13  # Processed clauses                    : 2366
% 0.92/1.13  # ...of these trivial                  : 4
% 0.92/1.13  # ...subsumed                          : 57
% 0.92/1.13  # ...remaining for further processing  : 2305
% 0.92/1.13  # Other redundant clauses eliminated   : 0
% 0.92/1.13  # Clauses deleted for lack of memory   : 0
% 0.92/1.13  # Backward-subsumed                    : 114
% 0.92/1.13  # Backward-rewritten                   : 567
% 0.92/1.13  # Generated clauses                    : 76027
% 0.92/1.13  # ...of the previous two non-trivial   : 75832
% 0.92/1.13  # Contextual simplify-reflections      : 4
% 0.92/1.13  # Paramodulations                      : 76027
% 0.92/1.13  # Factorizations                       : 0
% 0.92/1.13  # Equation resolutions                 : 0
% 0.92/1.13  # Propositional unsat checks           : 0
% 0.92/1.13  #    Propositional check models        : 0
% 0.92/1.13  #    Propositional check unsatisfiable : 0
% 0.92/1.13  #    Propositional clauses             : 0
% 0.92/1.13  #    Propositional clauses after purity: 0
% 0.92/1.13  #    Propositional unsat core size     : 0
% 0.92/1.13  #    Propositional preprocessing time  : 0.000
% 0.92/1.13  #    Propositional encoding time       : 0.000
% 0.92/1.13  #    Propositional solver time         : 0.000
% 0.92/1.13  #    Success case prop preproc time    : 0.000
% 0.92/1.13  #    Success case prop encoding time   : 0.000
% 0.92/1.13  #    Success case prop solver time     : 0.000
% 0.92/1.13  # Current number of processed clauses  : 1597
% 0.92/1.13  #    Positive orientable unit clauses  : 908
% 0.92/1.13  #    Positive unorientable unit clauses: 0
% 0.92/1.13  #    Negative unit clauses             : 5
% 0.92/1.13  #    Non-unit-clauses                  : 684
% 0.92/1.13  # Current number of unprocessed clauses: 73506
% 0.92/1.13  # ...number of literals in the above   : 238249
% 0.92/1.13  # Current number of archived formulas  : 0
% 0.92/1.13  # Current number of archived clauses   : 708
% 0.92/1.13  # Clause-clause subsumption calls (NU) : 151353
% 0.92/1.13  # Rec. Clause-clause subsumption calls : 49431
% 0.92/1.13  # Non-unit clause-clause subsumptions  : 174
% 0.92/1.13  # Unit Clause-clause subsumption calls : 50519
% 0.92/1.13  # Rewrite failures with RHS unbound    : 0
% 0.92/1.13  # BW rewrite match attempts            : 61355
% 0.92/1.13  # BW rewrite match successes           : 339
% 0.92/1.13  # Condensation attempts                : 0
% 0.92/1.13  # Condensation successes               : 0
% 0.92/1.13  # Termbank termtop insertions          : 3234220
% 0.92/1.13  
% 0.92/1.13  # -------------------------------------------------
% 0.92/1.13  # User time                : 0.747 s
% 0.92/1.13  # System time              : 0.044 s
% 0.92/1.13  # Total time               : 0.791 s
% 0.92/1.13  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

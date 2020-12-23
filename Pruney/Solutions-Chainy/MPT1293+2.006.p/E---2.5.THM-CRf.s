%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:52 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  123 (2652 expanded)
%              Number of clauses        :   86 (1278 expanded)
%              Number of leaves         :   18 ( 673 expanded)
%              Depth                    :   20
%              Number of atoms          :  211 (4625 expanded)
%              Number of equality atoms :   60 (1460 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t6_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_18,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_19,plain,(
    ! [X31,X32] : k3_tarski(k2_tarski(X31,X32)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k2_xboole_0(X22,X23))
      | r1_tarski(k4_xboole_0(X21,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_21,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | X28 = k2_xboole_0(X27,k4_xboole_0(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X19)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_27,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tops_2])).

fof(c_0_29,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ r1_tarski(X44,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X41,k1_zfmisc_1(X42))
        | r1_tarski(X41,X42) )
      & ( ~ r1_tarski(X41,X42)
        | m1_subset_1(X41,k1_zfmisc_1(X42)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_37,negated_conjecture,
    ( l1_struct_0(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & ~ r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k5_setfam_1(u1_struct_0(esk2_0),esk3_0),k5_setfam_1(u1_struct_0(esk2_0),esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),esk3_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( X2 = k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_23])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_42,plain,
    ( k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_23]),c_0_23])).

cnf(c_0_43,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_23]),c_0_23])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_47,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(k4_xboole_0(X24,X25),X26)
      | r1_tarski(X24,k2_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( k3_tarski(k2_tarski(k4_xboole_0(X1,X1),X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k4_xboole_0(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_39])).

fof(c_0_57,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_54,c_0_23])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X2,k4_xboole_0(X4,X4)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk4_0,k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),X1))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_60])).

cnf(c_0_67,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X3
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r1_tarski(k4_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_59]),c_0_42])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k4_xboole_0(X4,X4)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_66])).

cnf(c_0_72,plain,
    ( X1 = X2
    | ~ r1_tarski(k4_xboole_0(X2,X1),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))),X1),X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_59])).

fof(c_0_75,plain,(
    ! [X33,X34] : k3_tarski(k2_xboole_0(X33,X34)) = k2_xboole_0(k3_tarski(X33),k3_tarski(X34)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

cnf(c_0_76,negated_conjecture,
    ( X1 = k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_74])).

cnf(c_0_78,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) = k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,plain,
    ( k3_tarski(k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k3_tarski(X1),k3_tarski(X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_23]),c_0_23])).

fof(c_0_81,plain,(
    ! [X35] : k3_tarski(k1_zfmisc_1(X35)) = X35 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_82,negated_conjecture,
    ( X1 = k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_79]),c_0_79])).

cnf(c_0_83,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_39])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(k3_tarski(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k3_tarski(k2_tarski(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))) = k1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_52]),c_0_42])).

cnf(c_0_86,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_87,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k1_zfmisc_1(X39)))
      | k5_setfam_1(X39,X40) = k3_tarski(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k3_tarski(esk4_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_90,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_91,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k7_subset_1(X36,X37,X38) = k4_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) = k4_xboole_0(k3_tarski(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))) = k1_zfmisc_1(u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_66]),c_0_42])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_41])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k5_setfam_1(u1_struct_0(esk2_0),esk3_0),k5_setfam_1(u1_struct_0(esk2_0),esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_96,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk2_0),esk4_0) = k3_tarski(esk4_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_45])).

cnf(c_0_97,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk2_0),esk3_0) = k3_tarski(esk3_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_60])).

cnf(c_0_98,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_99,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_100,negated_conjecture,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(k3_tarski(esk4_0),u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_88,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k3_tarski(esk3_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_93]),c_0_86])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(k3_tarski(esk4_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_92])).

cnf(c_0_103,plain,
    ( k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_49])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k3_tarski(esk3_0),k3_tarski(esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),esk3_0,X1) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_60])).

cnf(c_0_106,plain,
    ( k5_setfam_1(X1,X2) = k3_tarski(X2)
    | ~ r1_tarski(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_66])).

fof(c_0_108,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_109,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( k4_xboole_0(k3_tarski(esk4_0),u1_struct_0(esk2_0)) = k4_xboole_0(k3_tarski(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_111,negated_conjecture,
    ( k3_tarski(k2_tarski(k3_tarski(esk4_0),u1_struct_0(esk2_0))) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_102]),c_0_103]),c_0_43])).

cnf(c_0_112,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k3_tarski(esk3_0),k3_tarski(esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),k4_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk2_0),X1) = k3_tarski(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_114,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_115,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X1,X2)),X1,X3) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_109,c_0_31])).

cnf(c_0_116,negated_conjecture,
    ( k3_tarski(k2_tarski(k3_tarski(esk3_0),u1_struct_0(esk2_0))) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_110]),c_0_42]),c_0_43]),c_0_111]),c_0_43])).

cnf(c_0_117,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k3_tarski(esk3_0),k3_tarski(esk4_0)),k3_tarski(k4_xboole_0(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])])).

cnf(c_0_118,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k3_tarski(esk3_0),X1) = k4_xboole_0(k3_tarski(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_119,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(X3))
    | ~ r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_80])).

cnf(c_0_120,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(esk3_0),k3_tarski(esk4_0)),k3_tarski(k4_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_121,plain,
    ( r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(k4_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_42])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_43]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:38:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.70/0.89  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.70/0.89  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.70/0.89  #
% 0.70/0.89  # Preprocessing time       : 0.017 s
% 0.70/0.89  # Presaturation interreduction done
% 0.70/0.89  
% 0.70/0.89  # Proof found!
% 0.70/0.89  # SZS status Theorem
% 0.70/0.89  # SZS output start CNFRefutation
% 0.70/0.89  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.70/0.89  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.70/0.89  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.70/0.89  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.70/0.89  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.70/0.89  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.70/0.89  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.70/0.89  fof(t6_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 0.70/0.89  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.70/0.89  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.70/0.89  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.70/0.89  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.70/0.89  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.70/0.89  fof(t96_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 0.70/0.89  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.70/0.89  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.70/0.89  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.70/0.89  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.70/0.89  fof(c_0_18, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.70/0.89  fof(c_0_19, plain, ![X31, X32]:k3_tarski(k2_tarski(X31,X32))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.70/0.89  fof(c_0_20, plain, ![X21, X22, X23]:(~r1_tarski(X21,k2_xboole_0(X22,X23))|r1_tarski(k4_xboole_0(X21,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.70/0.89  fof(c_0_21, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X15,X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.70/0.89  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.70/0.89  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.70/0.89  fof(c_0_24, plain, ![X27, X28]:(~r1_tarski(X27,X28)|X28=k2_xboole_0(X27,k4_xboole_0(X28,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.70/0.89  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.70/0.89  fof(c_0_26, plain, ![X19, X20]:k2_xboole_0(X19,k4_xboole_0(X20,X19))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.70/0.89  fof(c_0_27, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.70/0.89  fof(c_0_28, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))))))), inference(assume_negation,[status(cth)],[t6_tops_2])).
% 0.70/0.89  fof(c_0_29, plain, ![X43, X44]:(~r2_hidden(X43,X44)|~r1_tarski(X44,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.70/0.89  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.70/0.89  cnf(c_0_31, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.70/0.89  cnf(c_0_32, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.89  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_23])).
% 0.70/0.89  cnf(c_0_34, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.89  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.70/0.89  fof(c_0_36, plain, ![X41, X42]:((~m1_subset_1(X41,k1_zfmisc_1(X42))|r1_tarski(X41,X42))&(~r1_tarski(X41,X42)|m1_subset_1(X41,k1_zfmisc_1(X42)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.70/0.89  fof(c_0_37, negated_conjecture, (l1_struct_0(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&~r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k5_setfam_1(u1_struct_0(esk2_0),esk3_0),k5_setfam_1(u1_struct_0(esk2_0),esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.70/0.89  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.70/0.89  cnf(c_0_39, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.70/0.89  cnf(c_0_40, plain, (X2=k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_23])).
% 0.70/0.89  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.70/0.89  cnf(c_0_42, plain, (k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_23]), c_0_23])).
% 0.70/0.89  cnf(c_0_43, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_23]), c_0_23])).
% 0.70/0.89  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.70/0.89  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.70/0.89  fof(c_0_46, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.70/0.89  fof(c_0_47, plain, ![X24, X25, X26]:(~r1_tarski(k4_xboole_0(X24,X25),X26)|r1_tarski(X24,k2_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.70/0.89  cnf(c_0_48, plain, (~r2_hidden(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.70/0.89  cnf(c_0_49, plain, (k3_tarski(k2_tarski(k4_xboole_0(X1,X1),X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.70/0.89  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_43])).
% 0.70/0.89  cnf(c_0_51, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_30, c_0_39])).
% 0.70/0.89  cnf(c_0_52, negated_conjecture, (r1_tarski(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.70/0.89  cnf(c_0_53, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.70/0.89  cnf(c_0_54, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.70/0.89  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,k4_xboole_0(X3,X3))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.70/0.89  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_50, c_0_39])).
% 0.70/0.89  fof(c_0_57, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.70/0.89  cnf(c_0_58, negated_conjecture, (r1_tarski(esk4_0,k3_tarski(k2_tarski(X1,X2)))|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.70/0.89  cnf(c_0_59, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_53])).
% 0.70/0.89  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.70/0.89  cnf(c_0_61, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.70/0.89  cnf(c_0_62, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_54, c_0_23])).
% 0.70/0.89  cnf(c_0_63, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_tarski(X2,k4_xboole_0(X4,X4))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.70/0.89  cnf(c_0_64, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.70/0.89  cnf(c_0_65, negated_conjecture, (r1_tarski(esk4_0,k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),X1)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.70/0.89  cnf(c_0_66, negated_conjecture, (r1_tarski(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_44, c_0_60])).
% 0.70/0.89  cnf(c_0_67, plain, (k3_tarski(k2_tarski(X1,X2))=X3|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)|~r1_tarski(k4_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.70/0.89  cnf(c_0_68, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_59]), c_0_42])).
% 0.70/0.89  cnf(c_0_69, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k4_xboole_0(X4,X4))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.70/0.89  cnf(c_0_70, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))),X1)), inference(spm,[status(thm)],[c_0_33, c_0_65])).
% 0.70/0.89  cnf(c_0_71, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(k2_tarski(X1,X2)))|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),X1)), inference(spm,[status(thm)],[c_0_51, c_0_66])).
% 0.70/0.89  cnf(c_0_72, plain, (X1=X2|~r1_tarski(k4_xboole_0(X2,X1),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.70/0.89  cnf(c_0_73, negated_conjecture, (r1_tarski(k4_xboole_0(k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))),X1),X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.70/0.89  cnf(c_0_74, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(k2_tarski(k1_zfmisc_1(u1_struct_0(esk2_0)),X1)))), inference(spm,[status(thm)],[c_0_71, c_0_59])).
% 0.70/0.89  fof(c_0_75, plain, ![X33, X34]:k3_tarski(k2_xboole_0(X33,X34))=k2_xboole_0(k3_tarski(X33),k3_tarski(X34)), inference(variable_rename,[status(thm)],[t96_zfmisc_1])).
% 0.70/0.89  cnf(c_0_76, negated_conjecture, (X1=k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.70/0.89  cnf(c_0_77, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))),X1)), inference(spm,[status(thm)],[c_0_33, c_0_74])).
% 0.70/0.89  cnf(c_0_78, plain, (k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.70/0.89  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))=k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.70/0.89  cnf(c_0_80, plain, (k3_tarski(k3_tarski(k2_tarski(X1,X2)))=k3_tarski(k2_tarski(k3_tarski(X1),k3_tarski(X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_23]), c_0_23])).
% 0.70/0.89  fof(c_0_81, plain, ![X35]:k3_tarski(k1_zfmisc_1(X35))=X35, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.70/0.89  cnf(c_0_82, negated_conjecture, (X1=k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_79]), c_0_79])).
% 0.70/0.89  cnf(c_0_83, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_39])).
% 0.70/0.89  cnf(c_0_84, plain, (r1_tarski(k3_tarski(X1),k3_tarski(k3_tarski(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_31, c_0_80])).
% 0.70/0.89  cnf(c_0_85, negated_conjecture, (k3_tarski(k2_tarski(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))))=k1_zfmisc_1(u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_52]), c_0_42])).
% 0.70/0.89  cnf(c_0_86, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.70/0.89  fof(c_0_87, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k1_zfmisc_1(X39)))|k5_setfam_1(X39,X40)=k3_tarski(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.70/0.89  cnf(c_0_88, negated_conjecture, (k4_xboole_0(X1,X2)=k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.70/0.89  cnf(c_0_89, negated_conjecture, (r1_tarski(k3_tarski(esk4_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.70/0.89  cnf(c_0_90, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.70/0.89  fof(c_0_91, plain, ![X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|k7_subset_1(X36,X37,X38)=k4_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.70/0.89  cnf(c_0_92, negated_conjecture, (k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))=k4_xboole_0(k3_tarski(esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.70/0.89  cnf(c_0_93, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))))=k1_zfmisc_1(u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_66]), c_0_42])).
% 0.70/0.89  cnf(c_0_94, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_82, c_0_41])).
% 0.70/0.89  cnf(c_0_95, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k5_setfam_1(u1_struct_0(esk2_0),esk3_0),k5_setfam_1(u1_struct_0(esk2_0),esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.70/0.89  cnf(c_0_96, negated_conjecture, (k5_setfam_1(u1_struct_0(esk2_0),esk4_0)=k3_tarski(esk4_0)), inference(spm,[status(thm)],[c_0_90, c_0_45])).
% 0.70/0.89  cnf(c_0_97, negated_conjecture, (k5_setfam_1(u1_struct_0(esk2_0),esk3_0)=k3_tarski(esk3_0)), inference(spm,[status(thm)],[c_0_90, c_0_60])).
% 0.70/0.89  cnf(c_0_98, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.70/0.89  cnf(c_0_99, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.70/0.89  cnf(c_0_100, negated_conjecture, (k4_xboole_0(X1,X2)=k4_xboole_0(k3_tarski(esk4_0),u1_struct_0(esk2_0))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_88, c_0_92])).
% 0.70/0.89  cnf(c_0_101, negated_conjecture, (r1_tarski(k3_tarski(esk3_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_93]), c_0_86])).
% 0.70/0.89  cnf(c_0_102, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(k3_tarski(esk4_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_94, c_0_92])).
% 0.70/0.89  cnf(c_0_103, plain, (k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X2)))=X1), inference(spm,[status(thm)],[c_0_43, c_0_49])).
% 0.70/0.89  cnf(c_0_104, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k3_tarski(esk3_0),k3_tarski(esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_97])).
% 0.70/0.89  cnf(c_0_105, negated_conjecture, (k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),esk3_0,X1)=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_98, c_0_60])).
% 0.70/0.89  cnf(c_0_106, plain, (k5_setfam_1(X1,X2)=k3_tarski(X2)|~r1_tarski(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_90, c_0_99])).
% 0.70/0.89  cnf(c_0_107, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_66])).
% 0.70/0.89  fof(c_0_108, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.70/0.89  cnf(c_0_109, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.70/0.89  cnf(c_0_110, negated_conjecture, (k4_xboole_0(k3_tarski(esk4_0),u1_struct_0(esk2_0))=k4_xboole_0(k3_tarski(esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.70/0.89  cnf(c_0_111, negated_conjecture, (k3_tarski(k2_tarski(k3_tarski(esk4_0),u1_struct_0(esk2_0)))=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_102]), c_0_103]), c_0_43])).
% 0.70/0.89  cnf(c_0_112, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k3_tarski(esk3_0),k3_tarski(esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),k4_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_104, c_0_105])).
% 0.70/0.89  cnf(c_0_113, negated_conjecture, (k5_setfam_1(u1_struct_0(esk2_0),X1)=k3_tarski(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.70/0.89  cnf(c_0_114, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.70/0.89  cnf(c_0_115, plain, (k7_subset_1(k3_tarski(k2_tarski(X1,X2)),X1,X3)=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_109, c_0_31])).
% 0.70/0.89  cnf(c_0_116, negated_conjecture, (k3_tarski(k2_tarski(k3_tarski(esk3_0),u1_struct_0(esk2_0)))=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_110]), c_0_42]), c_0_43]), c_0_111]), c_0_43])).
% 0.70/0.89  cnf(c_0_117, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk2_0),k3_tarski(esk3_0),k3_tarski(esk4_0)),k3_tarski(k4_xboole_0(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])])).
% 0.70/0.89  cnf(c_0_118, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k3_tarski(esk3_0),X1)=k4_xboole_0(k3_tarski(esk3_0),X1)), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.70/0.89  cnf(c_0_119, plain, (r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(X3))|~r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_33, c_0_80])).
% 0.70/0.89  cnf(c_0_120, negated_conjecture, (~r1_tarski(k4_xboole_0(k3_tarski(esk3_0),k3_tarski(esk4_0)),k3_tarski(k4_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_117, c_0_118])).
% 0.70/0.89  cnf(c_0_121, plain, (r1_tarski(k4_xboole_0(X1,k3_tarski(X2)),k3_tarski(k4_xboole_0(X3,X2)))|~r1_tarski(X1,k3_tarski(k3_tarski(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_119, c_0_42])).
% 0.70/0.89  cnf(c_0_122, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_43]), c_0_84])]), ['proof']).
% 0.70/0.89  # SZS output end CNFRefutation
% 0.70/0.89  # Proof object total steps             : 123
% 0.70/0.89  # Proof object clause steps            : 86
% 0.70/0.89  # Proof object formula steps           : 37
% 0.70/0.89  # Proof object conjectures             : 41
% 0.70/0.89  # Proof object clause conjectures      : 38
% 0.70/0.89  # Proof object formula conjectures     : 3
% 0.70/0.89  # Proof object initial clauses used    : 22
% 0.70/0.89  # Proof object initial formulas used   : 18
% 0.70/0.89  # Proof object generating inferences   : 50
% 0.70/0.89  # Proof object simplifying inferences  : 36
% 0.70/0.89  # Training examples: 0 positive, 0 negative
% 0.70/0.89  # Parsed axioms                        : 18
% 0.70/0.89  # Removed by relevancy pruning/SinE    : 0
% 0.70/0.89  # Initial clauses                      : 26
% 0.70/0.89  # Removed in clause preprocessing      : 1
% 0.70/0.89  # Initial clauses in saturation        : 25
% 0.70/0.89  # Processed clauses                    : 4851
% 0.70/0.89  # ...of these trivial                  : 120
% 0.70/0.89  # ...subsumed                          : 3679
% 0.70/0.89  # ...remaining for further processing  : 1052
% 0.70/0.89  # Other redundant clauses eliminated   : 2
% 0.70/0.89  # Clauses deleted for lack of memory   : 0
% 0.70/0.89  # Backward-subsumed                    : 25
% 0.70/0.89  # Backward-rewritten                   : 54
% 0.70/0.89  # Generated clauses                    : 50761
% 0.70/0.89  # ...of the previous two non-trivial   : 44007
% 0.70/0.89  # Contextual simplify-reflections      : 0
% 0.70/0.89  # Paramodulations                      : 50756
% 0.70/0.89  # Factorizations                       : 0
% 0.70/0.89  # Equation resolutions                 : 2
% 0.70/0.89  # Propositional unsat checks           : 0
% 0.70/0.89  #    Propositional check models        : 0
% 0.70/0.89  #    Propositional check unsatisfiable : 0
% 0.70/0.89  #    Propositional clauses             : 0
% 0.70/0.89  #    Propositional clauses after purity: 0
% 0.70/0.89  #    Propositional unsat core size     : 0
% 0.70/0.89  #    Propositional preprocessing time  : 0.000
% 0.70/0.89  #    Propositional encoding time       : 0.000
% 0.70/0.89  #    Propositional solver time         : 0.000
% 0.70/0.89  #    Success case prop preproc time    : 0.000
% 0.70/0.89  #    Success case prop encoding time   : 0.000
% 0.70/0.89  #    Success case prop solver time     : 0.000
% 0.70/0.89  # Current number of processed clauses  : 946
% 0.70/0.89  #    Positive orientable unit clauses  : 202
% 0.70/0.89  #    Positive unorientable unit clauses: 11
% 0.70/0.89  #    Negative unit clauses             : 77
% 0.70/0.89  #    Non-unit-clauses                  : 656
% 0.70/0.89  # Current number of unprocessed clauses: 38542
% 0.70/0.89  # ...number of literals in the above   : 73989
% 0.70/0.89  # Current number of archived formulas  : 0
% 0.70/0.89  # Current number of archived clauses   : 104
% 0.70/0.89  # Clause-clause subsumption calls (NU) : 121272
% 0.70/0.89  # Rec. Clause-clause subsumption calls : 98828
% 0.70/0.89  # Non-unit clause-clause subsumptions  : 2245
% 0.70/0.89  # Unit Clause-clause subsumption calls : 12314
% 0.70/0.89  # Rewrite failures with RHS unbound    : 112
% 0.70/0.89  # BW rewrite match attempts            : 4867
% 0.70/0.89  # BW rewrite match successes           : 125
% 0.70/0.89  # Condensation attempts                : 0
% 0.70/0.89  # Condensation successes               : 0
% 0.70/0.89  # Termbank termtop insertions          : 845081
% 0.70/0.90  
% 0.70/0.90  # -------------------------------------------------
% 0.70/0.90  # User time                : 0.532 s
% 0.70/0.90  # System time              : 0.033 s
% 0.70/0.90  # Total time               : 0.565 s
% 0.70/0.90  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

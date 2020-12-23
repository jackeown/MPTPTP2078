%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:54 EST 2020

% Result     : Theorem 28.48s
% Output     : CNFRefutation 28.48s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 222 expanded)
%              Number of clauses        :   62 ( 102 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  222 ( 597 expanded)
%              Number of equality atoms :   33 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t50_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,k2_xboole_0(X28,X29))
      | r1_tarski(k4_xboole_0(X27,X28),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_20,plain,(
    ! [X33,X34] : r1_tarski(X33,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X22] : r1_tarski(k1_xboole_0,X22) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

fof(c_0_24,plain,(
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | ~ r1_tarski(X46,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X43,X44] :
      ( ( ~ m1_subset_1(X43,k1_zfmisc_1(X44))
        | r1_tarski(X43,X44) )
      & ( ~ r1_tarski(X43,X44)
        | m1_subset_1(X43,k1_zfmisc_1(X44)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ~ r1_tarski(k1_tops_1(esk2_0,k7_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X35,X36] :
      ( ( ~ r1_xboole_0(X35,X36)
        | k4_xboole_0(X35,X36) = X35 )
      & ( k4_xboole_0(X35,X36) != X35
        | r1_xboole_0(X35,X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_35,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X20,X21)
      | r1_tarski(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,plain,(
    ! [X47,X48] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
      | r1_tarski(k1_tops_1(X47,X48),X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_45,plain,
    ( ~ r1_xboole_0(X1,X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X1)
    | k1_xboole_0 != X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_47,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_51,plain,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_52,plain,
    ( k1_xboole_0 != X1
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_54,plain,(
    ! [X18] : k2_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_55,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | k7_subset_1(X40,X41,X42) = k4_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_37]),c_0_50])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_59,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(X12,X13)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_61,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | k1_xboole_0 != X1 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_61])).

cnf(c_0_70,plain,
    ( X1 = X2
    | k1_xboole_0 != X2
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_62])).

cnf(c_0_71,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk2_0,k7_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_74,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_37])).

cnf(c_0_75,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_77,plain,(
    ! [X30,X31,X32] :
      ( ( r1_xboole_0(X30,k2_xboole_0(X31,X32))
        | ~ r1_xboole_0(X30,X31)
        | ~ r1_xboole_0(X30,X32) )
      & ( r1_xboole_0(X30,X31)
        | ~ r1_xboole_0(X30,k2_xboole_0(X31,X32)) )
      & ( r1_xboole_0(X30,X32)
        | ~ r1_xboole_0(X30,k2_xboole_0(X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k1_tops_1(X1,k4_xboole_0(X2,X3)),X3)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k4_xboole_0(X2,X3),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_66])).

fof(c_0_80,plain,(
    ! [X25,X26] : k2_xboole_0(X25,k4_xboole_0(X26,X25)) = k2_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_72]),c_0_50])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),X1) = k4_xboole_0(k1_tops_1(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_85,plain,(
    ! [X37,X38,X39] :
      ( ~ r1_tarski(X37,X38)
      | ~ r1_xboole_0(X37,X39)
      | r1_tarski(X37,k4_xboole_0(X38,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_86,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_50])])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(k1_tops_1(esk2_0,esk4_0),esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,k2_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( k2_xboole_0(esk4_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_63])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k1_tops_1(esk2_0,esk4_0))
    | ~ r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k1_tops_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

fof(c_0_96,plain,(
    ! [X49,X50,X51] :
      ( ~ l1_pre_topc(X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
      | ~ r1_tarski(X50,X51)
      | r1_tarski(k1_tops_1(X49,X50),k1_tops_1(X49,X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k1_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_50]),c_0_37]),c_0_61])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_60]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 28.48/28.68  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 28.48/28.68  # and selection function SelectMaxLComplexAvoidPosPred.
% 28.48/28.68  #
% 28.48/28.68  # Preprocessing time       : 0.028 s
% 28.48/28.68  # Presaturation interreduction done
% 28.48/28.68  
% 28.48/28.68  # Proof found!
% 28.48/28.68  # SZS status Theorem
% 28.48/28.68  # SZS output start CNFRefutation
% 28.48/28.68  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 28.48/28.68  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 28.48/28.68  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 28.48/28.68  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 28.48/28.68  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tops_1)).
% 28.48/28.68  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 28.48/28.68  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 28.48/28.68  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 28.48/28.68  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 28.48/28.68  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 28.48/28.68  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 28.48/28.68  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 28.48/28.68  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 28.48/28.68  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 28.48/28.68  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 28.48/28.68  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 28.48/28.68  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 28.48/28.68  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 28.48/28.68  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 28.48/28.68  fof(c_0_19, plain, ![X27, X28, X29]:(~r1_tarski(X27,k2_xboole_0(X28,X29))|r1_tarski(k4_xboole_0(X27,X28),X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 28.48/28.68  fof(c_0_20, plain, ![X33, X34]:r1_tarski(X33,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 28.48/28.68  fof(c_0_21, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 28.48/28.68  fof(c_0_22, plain, ![X22]:r1_tarski(k1_xboole_0,X22), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 28.48/28.68  fof(c_0_23, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 28.48/28.68  fof(c_0_24, plain, ![X45, X46]:(~r2_hidden(X45,X46)|~r1_tarski(X46,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 28.48/28.68  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 28.48/28.68  cnf(c_0_26, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 28.48/28.68  cnf(c_0_27, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 28.48/28.68  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 28.48/28.68  fof(c_0_29, plain, ![X43, X44]:((~m1_subset_1(X43,k1_zfmisc_1(X44))|r1_tarski(X43,X44))&(~r1_tarski(X43,X44)|m1_subset_1(X43,k1_zfmisc_1(X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 28.48/28.68  fof(c_0_30, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&~r1_tarski(k1_tops_1(esk2_0,k7_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 28.48/28.68  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 28.48/28.68  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 28.48/28.68  fof(c_0_33, plain, ![X35, X36]:((~r1_xboole_0(X35,X36)|k4_xboole_0(X35,X36)=X35)&(k4_xboole_0(X35,X36)!=X35|r1_xboole_0(X35,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 28.48/28.68  cnf(c_0_34, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 28.48/28.68  fof(c_0_35, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X20,X21)|r1_tarski(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 28.48/28.68  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 28.48/28.68  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 28.48/28.68  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 28.48/28.68  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 28.48/28.68  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 28.48/28.68  cnf(c_0_41, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 28.48/28.68  cnf(c_0_42, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 28.48/28.68  cnf(c_0_43, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 28.48/28.68  fof(c_0_44, plain, ![X47, X48]:(~l1_pre_topc(X47)|(~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|r1_tarski(k1_tops_1(X47,X48),X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 28.48/28.68  cnf(c_0_45, plain, (~r1_xboole_0(X1,X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 28.48/28.68  cnf(c_0_46, plain, (r1_xboole_0(X1,X1)|k1_xboole_0!=X1), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 28.48/28.68  fof(c_0_47, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 28.48/28.68  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 28.48/28.68  cnf(c_0_49, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 28.48/28.68  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 28.48/28.68  fof(c_0_51, plain, ![X23, X24]:r1_tarski(k4_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 28.48/28.68  cnf(c_0_52, plain, (k1_xboole_0!=X1|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 28.48/28.68  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 28.48/28.68  fof(c_0_54, plain, ![X18]:k2_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t1_boole])).
% 28.48/28.68  fof(c_0_55, plain, ![X40, X41, X42]:(~m1_subset_1(X41,k1_zfmisc_1(X40))|k7_subset_1(X40,X41,X42)=k4_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 28.48/28.68  cnf(c_0_56, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_48])).
% 28.48/28.68  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_37]), c_0_50])])).
% 28.48/28.68  cnf(c_0_58, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 28.48/28.68  fof(c_0_59, plain, ![X12, X13, X14]:((r1_tarski(X12,X13)|~r1_tarski(X12,k4_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_tarski(X12,k4_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 28.48/28.68  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 28.48/28.68  cnf(c_0_61, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 28.48/28.68  cnf(c_0_62, plain, (r1_tarski(X1,X2)|k1_xboole_0!=X1), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 28.48/28.68  cnf(c_0_63, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 28.48/28.68  cnf(c_0_64, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 28.48/28.68  cnf(c_0_65, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 28.48/28.68  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_58])).
% 28.48/28.68  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 28.48/28.68  cnf(c_0_68, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_49, c_0_60])).
% 28.48/28.68  cnf(c_0_69, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,k4_xboole_0(esk3_0,X2))), inference(spm,[status(thm)],[c_0_56, c_0_61])).
% 28.48/28.68  cnf(c_0_70, plain, (X1=X2|k1_xboole_0!=X2|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_62])).
% 28.48/28.68  cnf(c_0_71, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_63])).
% 28.48/28.68  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 28.48/28.68  cnf(c_0_73, negated_conjecture, (~r1_tarski(k1_tops_1(esk2_0,k7_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 28.48/28.68  cnf(c_0_74, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),esk3_0,X1)=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_37])).
% 28.48/28.68  cnf(c_0_75, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_64, c_0_60])).
% 28.48/28.68  cnf(c_0_76, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 28.48/28.68  fof(c_0_77, plain, ![X30, X31, X32]:((r1_xboole_0(X30,k2_xboole_0(X31,X32))|~r1_xboole_0(X30,X31)|~r1_xboole_0(X30,X32))&((r1_xboole_0(X30,X31)|~r1_xboole_0(X30,k2_xboole_0(X31,X32)))&(r1_xboole_0(X30,X32)|~r1_xboole_0(X30,k2_xboole_0(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 28.48/28.68  cnf(c_0_78, plain, (r1_xboole_0(k1_tops_1(X1,k4_xboole_0(X2,X3)),X3)|~l1_pre_topc(X1)|~r1_tarski(k4_xboole_0(X2,X3),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 28.48/28.68  cnf(c_0_79, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_69, c_0_66])).
% 28.48/28.68  fof(c_0_80, plain, ![X25, X26]:k2_xboole_0(X25,k4_xboole_0(X26,X25))=k2_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 28.48/28.68  cnf(c_0_81, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 28.48/28.68  cnf(c_0_82, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_72]), c_0_50])])).
% 28.48/28.68  cnf(c_0_83, negated_conjecture, (~r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0)))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 28.48/28.68  cnf(c_0_84, negated_conjecture, (k7_subset_1(u1_struct_0(esk2_0),k1_tops_1(esk2_0,esk3_0),X1)=k4_xboole_0(k1_tops_1(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 28.48/28.68  fof(c_0_85, plain, ![X37, X38, X39]:(~r1_tarski(X37,X38)|~r1_xboole_0(X37,X39)|r1_tarski(X37,k4_xboole_0(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 28.48/28.68  cnf(c_0_86, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 28.48/28.68  cnf(c_0_87, negated_conjecture, (r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_50])])).
% 28.48/28.68  cnf(c_0_88, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 28.48/28.68  cnf(c_0_89, negated_conjecture, (k4_xboole_0(k1_tops_1(esk2_0,esk4_0),esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 28.48/28.68  cnf(c_0_90, negated_conjecture, (~r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(k1_tops_1(esk2_0,esk3_0),k1_tops_1(esk2_0,esk4_0)))), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 28.48/28.68  cnf(c_0_91, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 28.48/28.68  cnf(c_0_92, negated_conjecture, (r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,k2_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 28.48/28.68  cnf(c_0_93, negated_conjecture, (k2_xboole_0(esk4_0,k1_tops_1(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_63])).
% 28.48/28.68  cnf(c_0_94, negated_conjecture, (~r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k1_tops_1(esk2_0,esk4_0))|~r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 28.48/28.68  cnf(c_0_95, negated_conjecture, (r1_xboole_0(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k1_tops_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 28.48/28.68  fof(c_0_96, plain, ![X49, X50, X51]:(~l1_pre_topc(X49)|(~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|(~r1_tarski(X50,X51)|r1_tarski(k1_tops_1(X49,X50),k1_tops_1(X49,X51)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 28.48/28.68  cnf(c_0_97, negated_conjecture, (~r1_tarski(k1_tops_1(esk2_0,k4_xboole_0(esk3_0,esk4_0)),k1_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 28.48/28.68  cnf(c_0_98, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 28.48/28.68  cnf(c_0_99, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_50]), c_0_37]), c_0_61])])).
% 28.48/28.68  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_60]), c_0_79])]), ['proof']).
% 28.48/28.68  # SZS output end CNFRefutation
% 28.48/28.68  # Proof object total steps             : 101
% 28.48/28.68  # Proof object clause steps            : 62
% 28.48/28.68  # Proof object formula steps           : 39
% 28.48/28.68  # Proof object conjectures             : 29
% 28.48/28.68  # Proof object clause conjectures      : 26
% 28.48/28.68  # Proof object formula conjectures     : 3
% 28.48/28.68  # Proof object initial clauses used    : 25
% 28.48/28.68  # Proof object initial formulas used   : 19
% 28.48/28.68  # Proof object generating inferences   : 33
% 28.48/28.68  # Proof object simplifying inferences  : 18
% 28.48/28.68  # Training examples: 0 positive, 0 negative
% 28.48/28.68  # Parsed axioms                        : 20
% 28.48/28.68  # Removed by relevancy pruning/SinE    : 0
% 28.48/28.68  # Initial clauses                      : 33
% 28.48/28.68  # Removed in clause preprocessing      : 0
% 28.48/28.68  # Initial clauses in saturation        : 33
% 28.48/28.68  # Processed clauses                    : 98768
% 28.48/28.68  # ...of these trivial                  : 878
% 28.48/28.68  # ...subsumed                          : 90694
% 28.48/28.68  # ...remaining for further processing  : 7196
% 28.48/28.68  # Other redundant clauses eliminated   : 6
% 28.48/28.68  # Clauses deleted for lack of memory   : 69490
% 28.48/28.68  # Backward-subsumed                    : 406
% 28.48/28.68  # Backward-rewritten                   : 16
% 28.48/28.68  # Generated clauses                    : 3150607
% 28.48/28.68  # ...of the previous two non-trivial   : 2599377
% 28.48/28.68  # Contextual simplify-reflections      : 179
% 28.48/28.68  # Paramodulations                      : 3150537
% 28.48/28.68  # Factorizations                       : 0
% 28.48/28.68  # Equation resolutions                 : 64
% 28.48/28.68  # Propositional unsat checks           : 0
% 28.48/28.68  #    Propositional check models        : 0
% 28.48/28.68  #    Propositional check unsatisfiable : 0
% 28.48/28.68  #    Propositional clauses             : 0
% 28.48/28.68  #    Propositional clauses after purity: 0
% 28.48/28.68  #    Propositional unsat core size     : 0
% 28.48/28.68  #    Propositional preprocessing time  : 0.000
% 28.48/28.68  #    Propositional encoding time       : 0.000
% 28.48/28.68  #    Propositional solver time         : 0.000
% 28.48/28.68  #    Success case prop preproc time    : 0.000
% 28.48/28.68  #    Success case prop encoding time   : 0.000
% 28.48/28.68  #    Success case prop solver time     : 0.000
% 28.48/28.68  # Current number of processed clauses  : 6738
% 28.48/28.68  #    Positive orientable unit clauses  : 828
% 28.48/28.68  #    Positive unorientable unit clauses: 0
% 28.48/28.68  #    Negative unit clauses             : 144
% 28.48/28.68  #    Non-unit-clauses                  : 5766
% 28.48/28.68  # Current number of unprocessed clauses: 1270904
% 28.48/28.68  # ...number of literals in the above   : 3930737
% 28.48/28.68  # Current number of archived formulas  : 0
% 28.48/28.68  # Current number of archived clauses   : 454
% 28.48/28.68  # Clause-clause subsumption calls (NU) : 13806568
% 28.48/28.68  # Rec. Clause-clause subsumption calls : 7128171
% 28.48/28.68  # Non-unit clause-clause subsumptions  : 57760
% 28.48/28.68  # Unit Clause-clause subsumption calls : 179540
% 28.48/28.68  # Rewrite failures with RHS unbound    : 0
% 28.48/28.68  # BW rewrite match attempts            : 55897
% 28.48/28.68  # BW rewrite match successes           : 15
% 28.48/28.68  # Condensation attempts                : 0
% 28.48/28.68  # Condensation successes               : 0
% 28.48/28.68  # Termbank termtop insertions          : 53888800
% 28.55/28.76  
% 28.55/28.76  # -------------------------------------------------
% 28.55/28.76  # User time                : 27.424 s
% 28.55/28.76  # System time              : 0.974 s
% 28.55/28.76  # Total time               : 28.399 s
% 28.55/28.76  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

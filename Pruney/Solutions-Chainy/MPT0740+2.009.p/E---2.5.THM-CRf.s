%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:12 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 412 expanded)
%              Number of clauses        :   51 ( 188 expanded)
%              Number of leaves         :   12 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          :  217 (1248 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t30_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(t22_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ! [X3] :
              ( v3_ordinal1(X3)
             => ( ( r1_tarski(X1,X2)
                  & r2_hidden(X2,X3) )
               => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_12,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v3_ordinal1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t30_ordinal1])).

fof(c_0_14,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_ordinal1(X25)
      | ~ v3_ordinal1(X26)
      | ~ v3_ordinal1(X27)
      | ~ r1_tarski(X25,X26)
      | ~ r2_hidden(X26,X27)
      | r2_hidden(X25,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( ~ v3_ordinal1(X29)
      | ~ r2_hidden(X28,X29)
      | v3_ordinal1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_16,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(k3_tarski(X13),X14)
      | ~ r2_hidden(X15,X13)
      | r1_tarski(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ~ v3_ordinal1(X16)
      | ~ v3_ordinal1(X17)
      | r1_ordinal1(X16,X17)
      | r1_ordinal1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_20,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & ~ v3_ordinal1(k3_tarski(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X24] : r2_hidden(X24,k1_ordinal1(X24)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v1_ordinal1(X18)
        | ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X18) )
      & ( r2_hidden(esk3_1(X20),X20)
        | v1_ordinal1(X20) )
      & ( ~ r1_tarski(esk3_1(X20),X20)
        | v1_ordinal1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_27,plain,(
    ! [X10,X11] :
      ( ( r2_hidden(esk2_2(X10,X11),X10)
        | r1_tarski(k3_tarski(X10),X11) )
      & ( ~ r1_tarski(esk2_2(X10,X11),X11)
        | r1_tarski(k3_tarski(X10),X11) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_28,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X30] :
      ( ~ v3_ordinal1(X30)
      | v3_ordinal1(k1_ordinal1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_39,plain,(
    ! [X22,X23] :
      ( ( ~ r1_ordinal1(X22,X23)
        | r1_tarski(X22,X23)
        | ~ v3_ordinal1(X22)
        | ~ v3_ordinal1(X23) )
      & ( ~ r1_tarski(X22,X23)
        | r1_ordinal1(X22,X23)
        | ~ v3_ordinal1(X22)
        | ~ v3_ordinal1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_ordinal1(X1,esk4_0)
    | r1_ordinal1(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ r2_hidden(esk3_1(k3_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( v1_ordinal1(X1)
    | r2_hidden(esk3_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,plain,
    ( r1_tarski(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_47,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ r1_tarski(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_ordinal1(esk4_0,k1_ordinal1(X1))
    | r1_ordinal1(k1_ordinal1(X1),esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_51,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(k1_ordinal1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_42])).

cnf(c_0_52,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ r1_tarski(k3_tarski(X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(k3_tarski(X1),X1)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_ordinal1(esk4_0,k1_ordinal1(X1))
    | r1_tarski(k1_ordinal1(X1),esk4_0)
    | ~ v3_ordinal1(k1_ordinal1(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_29])]),c_0_50])).

cnf(c_0_56,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_41])).

cnf(c_0_57,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( ~ r1_tarski(k1_ordinal1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k1_ordinal1(X1),esk4_0)
    | r1_tarski(esk4_0,k1_ordinal1(X1))
    | ~ v3_ordinal1(k1_ordinal1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_55]),c_0_29])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_61,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_57])).

cnf(c_0_62,plain,
    ( v1_ordinal1(X1)
    | v3_ordinal1(esk3_1(X1))
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk4_0,k1_ordinal1(esk4_0))
    | ~ v3_ordinal1(k1_ordinal1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_ordinal1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_29])])).

cnf(c_0_65,negated_conjecture,
    ( v3_ordinal1(esk3_1(esk4_0))
    | ~ v3_ordinal1(k1_ordinal1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( r1_ordinal1(X1,esk3_1(esk4_0))
    | r1_ordinal1(esk3_1(esk4_0),X1)
    | ~ v3_ordinal1(k1_ordinal1(esk4_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( r1_ordinal1(esk3_1(esk4_0),X1)
    | r1_ordinal1(X1,esk3_1(esk4_0))
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_41]),c_0_29])])).

cnf(c_0_68,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk3_1(esk4_0))
    | r1_ordinal1(esk3_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk3_1(esk4_0))
    | r1_tarski(esk3_1(esk4_0),esk4_0)
    | ~ v3_ordinal1(esk3_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_68]),c_0_29])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_1(esk4_0),esk4_0)
    | r1_tarski(esk4_0,esk3_1(esk4_0))
    | ~ v3_ordinal1(esk3_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_69]),c_0_29])])).

cnf(c_0_71,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(X1,esk3_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_1(esk4_0))
    | ~ v3_ordinal1(esk3_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_70]),c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( ~ v3_ordinal1(esk3_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_64])).

cnf(c_0_74,plain,
    ( v1_ordinal1(X1)
    | v3_ordinal1(esk3_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_29])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.70  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PI_PS_S5PRR_S032N
% 0.46/0.70  # and selection function SelectUnlessUniqMax.
% 0.46/0.70  #
% 0.46/0.70  # Preprocessing time       : 0.029 s
% 0.46/0.70  # Presaturation interreduction done
% 0.46/0.70  
% 0.46/0.70  # Proof found!
% 0.46/0.70  # SZS status Theorem
% 0.46/0.70  # SZS output start CNFRefutation
% 0.46/0.70  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.46/0.70  fof(t30_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_ordinal1)).
% 0.46/0.70  fof(t22_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r1_tarski(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 0.46/0.70  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.46/0.70  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.46/0.70  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.46/0.70  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.46/0.70  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.46/0.70  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.46/0.70  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.46/0.70  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.46/0.70  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.46/0.70  fof(c_0_12, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.46/0.70  fof(c_0_13, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t30_ordinal1])).
% 0.46/0.70  fof(c_0_14, plain, ![X25, X26, X27]:(~v1_ordinal1(X25)|(~v3_ordinal1(X26)|(~v3_ordinal1(X27)|(~r1_tarski(X25,X26)|~r2_hidden(X26,X27)|r2_hidden(X25,X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).
% 0.46/0.70  fof(c_0_15, plain, ![X28, X29]:(~v3_ordinal1(X29)|(~r2_hidden(X28,X29)|v3_ordinal1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.46/0.70  fof(c_0_16, plain, ![X13, X14, X15]:(~r1_tarski(k3_tarski(X13),X14)|~r2_hidden(X15,X13)|r1_tarski(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.46/0.70  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.46/0.70  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.46/0.70  fof(c_0_19, plain, ![X16, X17]:(~v3_ordinal1(X16)|~v3_ordinal1(X17)|(r1_ordinal1(X16,X17)|r1_ordinal1(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.46/0.70  fof(c_0_20, negated_conjecture, (v3_ordinal1(esk4_0)&~v3_ordinal1(k3_tarski(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.46/0.70  cnf(c_0_21, plain, (r2_hidden(X1,X3)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~v3_ordinal1(X3)|~r1_tarski(X1,X2)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.46/0.70  cnf(c_0_22, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.70  fof(c_0_23, plain, ![X24]:r2_hidden(X24,k1_ordinal1(X24)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.46/0.70  fof(c_0_24, plain, ![X18, X19, X20]:((~v1_ordinal1(X18)|(~r2_hidden(X19,X18)|r1_tarski(X19,X18)))&((r2_hidden(esk3_1(X20),X20)|v1_ordinal1(X20))&(~r1_tarski(esk3_1(X20),X20)|v1_ordinal1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.46/0.70  cnf(c_0_25, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.70  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.46/0.70  fof(c_0_27, plain, ![X10, X11]:((r2_hidden(esk2_2(X10,X11),X10)|r1_tarski(k3_tarski(X10),X11))&(~r1_tarski(esk2_2(X10,X11),X11)|r1_tarski(k3_tarski(X10),X11))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.46/0.70  cnf(c_0_28, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.70  cnf(c_0_29, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.70  fof(c_0_30, plain, ![X30]:(~v3_ordinal1(X30)|v3_ordinal1(k1_ordinal1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.46/0.70  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X3,X2)|~r1_tarski(X1,X3)), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.46/0.70  cnf(c_0_32, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.46/0.70  cnf(c_0_33, plain, (v1_ordinal1(X1)|~r1_tarski(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.70  cnf(c_0_34, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.46/0.70  cnf(c_0_35, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.46/0.70  cnf(c_0_36, plain, (r2_hidden(esk3_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.70  cnf(c_0_37, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.70  cnf(c_0_38, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.46/0.70  fof(c_0_39, plain, ![X22, X23]:((~r1_ordinal1(X22,X23)|r1_tarski(X22,X23)|(~v3_ordinal1(X22)|~v3_ordinal1(X23)))&(~r1_tarski(X22,X23)|r1_ordinal1(X22,X23)|(~v3_ordinal1(X22)|~v3_ordinal1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.46/0.70  cnf(c_0_40, negated_conjecture, (r1_ordinal1(X1,esk4_0)|r1_ordinal1(esk4_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.46/0.70  cnf(c_0_41, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.46/0.70  cnf(c_0_42, plain, (r2_hidden(X1,k1_ordinal1(X2))|~v1_ordinal1(X1)|~v3_ordinal1(k1_ordinal1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.46/0.70  cnf(c_0_43, plain, (v1_ordinal1(k3_tarski(X1))|~r2_hidden(esk3_1(k3_tarski(X1)),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.46/0.70  cnf(c_0_44, plain, (v1_ordinal1(X1)|r2_hidden(esk3_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.46/0.70  cnf(c_0_45, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.46/0.70  cnf(c_0_46, plain, (r1_tarski(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.46/0.70  fof(c_0_47, plain, ![X31, X32]:(~r2_hidden(X31,X32)|~r1_tarski(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.46/0.70  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.46/0.70  cnf(c_0_49, negated_conjecture, (r1_ordinal1(esk4_0,k1_ordinal1(X1))|r1_ordinal1(k1_ordinal1(X1),esk4_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.46/0.70  cnf(c_0_50, plain, (v3_ordinal1(X1)|~v3_ordinal1(k1_ordinal1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_32])).
% 0.46/0.70  cnf(c_0_51, plain, (v3_ordinal1(X1)|~v1_ordinal1(X1)|~v3_ordinal1(k1_ordinal1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_42])).
% 0.46/0.70  cnf(c_0_52, plain, (v1_ordinal1(k3_tarski(X1))|~r1_tarski(k3_tarski(X1),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.46/0.71  cnf(c_0_53, plain, (r1_tarski(k3_tarski(X1),X1)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.46/0.71  cnf(c_0_54, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.46/0.71  cnf(c_0_55, negated_conjecture, (r1_ordinal1(esk4_0,k1_ordinal1(X1))|r1_tarski(k1_ordinal1(X1),esk4_0)|~v3_ordinal1(k1_ordinal1(X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_29])]), c_0_50])).
% 0.46/0.71  cnf(c_0_56, plain, (v3_ordinal1(X1)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_41])).
% 0.46/0.71  cnf(c_0_57, plain, (v1_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.46/0.71  cnf(c_0_58, plain, (~r1_tarski(k1_ordinal1(X1),X1)), inference(spm,[status(thm)],[c_0_54, c_0_32])).
% 0.46/0.71  cnf(c_0_59, negated_conjecture, (r1_tarski(k1_ordinal1(X1),esk4_0)|r1_tarski(esk4_0,k1_ordinal1(X1))|~v3_ordinal1(k1_ordinal1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_55]), c_0_29])])).
% 0.46/0.71  cnf(c_0_60, negated_conjecture, (~v3_ordinal1(k3_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.71  cnf(c_0_61, plain, (v3_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_57])).
% 0.46/0.71  cnf(c_0_62, plain, (v1_ordinal1(X1)|v3_ordinal1(esk3_1(X1))|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_44])).
% 0.46/0.71  cnf(c_0_63, negated_conjecture, (r1_tarski(esk4_0,k1_ordinal1(esk4_0))|~v3_ordinal1(k1_ordinal1(esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.46/0.71  cnf(c_0_64, negated_conjecture, (~v1_ordinal1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_29])])).
% 0.46/0.71  cnf(c_0_65, negated_conjecture, (v3_ordinal1(esk3_1(esk4_0))|~v3_ordinal1(k1_ordinal1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.46/0.71  cnf(c_0_66, negated_conjecture, (r1_ordinal1(X1,esk3_1(esk4_0))|r1_ordinal1(esk3_1(esk4_0),X1)|~v3_ordinal1(k1_ordinal1(esk4_0))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_65])).
% 0.46/0.71  cnf(c_0_67, negated_conjecture, (r1_ordinal1(esk3_1(esk4_0),X1)|r1_ordinal1(X1,esk3_1(esk4_0))|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_41]), c_0_29])])).
% 0.46/0.71  cnf(c_0_68, negated_conjecture, (r1_ordinal1(esk4_0,esk3_1(esk4_0))|r1_ordinal1(esk3_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_29])).
% 0.46/0.71  cnf(c_0_69, negated_conjecture, (r1_ordinal1(esk4_0,esk3_1(esk4_0))|r1_tarski(esk3_1(esk4_0),esk4_0)|~v3_ordinal1(esk3_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_68]), c_0_29])])).
% 0.46/0.71  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_1(esk4_0),esk4_0)|r1_tarski(esk4_0,esk3_1(esk4_0))|~v3_ordinal1(esk3_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_69]), c_0_29])])).
% 0.46/0.71  cnf(c_0_71, plain, (v1_ordinal1(X1)|~r1_tarski(X1,esk3_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_36])).
% 0.46/0.71  cnf(c_0_72, negated_conjecture, (r1_tarski(esk4_0,esk3_1(esk4_0))|~v3_ordinal1(esk3_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_70]), c_0_64])).
% 0.46/0.71  cnf(c_0_73, negated_conjecture, (~v3_ordinal1(esk3_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_64])).
% 0.46/0.71  cnf(c_0_74, plain, (v1_ordinal1(X1)|v3_ordinal1(esk3_1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_36])).
% 0.46/0.71  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_29])]), c_0_64]), ['proof']).
% 0.46/0.71  # SZS output end CNFRefutation
% 0.46/0.71  # Proof object total steps             : 76
% 0.46/0.71  # Proof object clause steps            : 51
% 0.46/0.71  # Proof object formula steps           : 25
% 0.46/0.71  # Proof object conjectures             : 20
% 0.46/0.71  # Proof object clause conjectures      : 17
% 0.46/0.71  # Proof object formula conjectures     : 3
% 0.46/0.71  # Proof object initial clauses used    : 18
% 0.46/0.71  # Proof object initial formulas used   : 12
% 0.46/0.71  # Proof object generating inferences   : 32
% 0.46/0.71  # Proof object simplifying inferences  : 21
% 0.46/0.71  # Training examples: 0 positive, 0 negative
% 0.46/0.71  # Parsed axioms                        : 12
% 0.46/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.71  # Initial clauses                      : 19
% 0.46/0.71  # Removed in clause preprocessing      : 0
% 0.46/0.71  # Initial clauses in saturation        : 19
% 0.46/0.71  # Processed clauses                    : 2720
% 0.46/0.71  # ...of these trivial                  : 5
% 0.46/0.71  # ...subsumed                          : 1369
% 0.46/0.71  # ...remaining for further processing  : 1346
% 0.46/0.71  # Other redundant clauses eliminated   : 0
% 0.46/0.71  # Clauses deleted for lack of memory   : 0
% 0.46/0.71  # Backward-subsumed                    : 33
% 0.46/0.71  # Backward-rewritten                   : 0
% 0.46/0.71  # Generated clauses                    : 19670
% 0.46/0.71  # ...of the previous two non-trivial   : 19534
% 0.46/0.71  # Contextual simplify-reflections      : 21
% 0.46/0.71  # Paramodulations                      : 19669
% 0.46/0.71  # Factorizations                       : 0
% 0.46/0.71  # Equation resolutions                 : 0
% 0.46/0.71  # Propositional unsat checks           : 0
% 0.46/0.71  #    Propositional check models        : 0
% 0.46/0.71  #    Propositional check unsatisfiable : 0
% 0.46/0.71  #    Propositional clauses             : 0
% 0.46/0.71  #    Propositional clauses after purity: 0
% 0.46/0.71  #    Propositional unsat core size     : 0
% 0.46/0.71  #    Propositional preprocessing time  : 0.000
% 0.46/0.71  #    Propositional encoding time       : 0.000
% 0.46/0.71  #    Propositional solver time         : 0.000
% 0.46/0.71  #    Success case prop preproc time    : 0.000
% 0.46/0.71  #    Success case prop encoding time   : 0.000
% 0.46/0.71  #    Success case prop solver time     : 0.000
% 0.46/0.71  # Current number of processed clauses  : 1293
% 0.46/0.71  #    Positive orientable unit clauses  : 21
% 0.46/0.71  #    Positive unorientable unit clauses: 0
% 0.46/0.71  #    Negative unit clauses             : 185
% 0.46/0.71  #    Non-unit-clauses                  : 1087
% 0.46/0.71  # Current number of unprocessed clauses: 16825
% 0.46/0.71  # ...number of literals in the above   : 53895
% 0.46/0.71  # Current number of archived formulas  : 0
% 0.46/0.71  # Current number of archived clauses   : 53
% 0.46/0.71  # Clause-clause subsumption calls (NU) : 127975
% 0.46/0.71  # Rec. Clause-clause subsumption calls : 59133
% 0.46/0.71  # Non-unit clause-clause subsumptions  : 1073
% 0.46/0.71  # Unit Clause-clause subsumption calls : 14344
% 0.46/0.71  # Rewrite failures with RHS unbound    : 0
% 0.46/0.71  # BW rewrite match attempts            : 75
% 0.46/0.71  # BW rewrite match successes           : 0
% 0.46/0.71  # Condensation attempts                : 0
% 0.46/0.71  # Condensation successes               : 0
% 0.46/0.71  # Termbank termtop insertions          : 446507
% 0.46/0.71  
% 0.46/0.71  # -------------------------------------------------
% 0.46/0.71  # User time                : 0.348 s
% 0.46/0.71  # System time              : 0.017 s
% 0.46/0.71  # Total time               : 0.365 s
% 0.46/0.71  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

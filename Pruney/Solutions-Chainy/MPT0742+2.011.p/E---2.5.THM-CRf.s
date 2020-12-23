%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:15 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   46 (  92 expanded)
%              Number of clauses        :   27 (  38 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 402 expanded)
%              Number of equality atoms :    9 (  30 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_ordinal1,conjecture,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ~ ( r1_tarski(X1,X2)
          & X1 != k1_xboole_0
          & ! [X3] :
              ( v3_ordinal1(X3)
             => ~ ( r2_hidden(X3,X1)
                  & ! [X4] :
                      ( v3_ordinal1(X4)
                     => ( r2_hidden(X4,X1)
                       => r1_ordinal1(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v3_ordinal1(X2)
       => ~ ( r1_tarski(X1,X2)
            & X1 != k1_xboole_0
            & ! [X3] :
                ( v3_ordinal1(X3)
               => ~ ( r2_hidden(X3,X1)
                    & ! [X4] :
                        ( v3_ordinal1(X4)
                       => ( r2_hidden(X4,X1)
                         => r1_ordinal1(X3,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_ordinal1])).

fof(c_0_10,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_11,negated_conjecture,(
    ! [X26] :
      ( v3_ordinal1(esk4_0)
      & r1_tarski(esk3_0,esk4_0)
      & esk3_0 != k1_xboole_0
      & ( v3_ordinal1(esk5_1(X26))
        | ~ r2_hidden(X26,esk3_0)
        | ~ v3_ordinal1(X26) )
      & ( r2_hidden(esk5_1(X26),esk3_0)
        | ~ r2_hidden(X26,esk3_0)
        | ~ v3_ordinal1(X26) )
      & ( ~ r1_ordinal1(X26,esk5_1(X26))
        | ~ r2_hidden(X26,esk3_0)
        | ~ v3_ordinal1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ( ~ r1_tarski(k1_tarski(X12),X13)
        | r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X12,X13)
        | r1_tarski(k1_tarski(X12),X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_17,plain,(
    ! [X20,X21] :
      ( ~ v3_ordinal1(X20)
      | ~ v3_ordinal1(X21)
      | r1_ordinal1(X20,X21)
      | r2_hidden(X21,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ~ v3_ordinal1(X19)
      | ~ r2_hidden(X18,X19)
      | v3_ordinal1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r1_tarski(k1_tarski(X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X14,X15,X17] :
      ( ( r2_hidden(esk2_2(X14,X15),X15)
        | ~ r2_hidden(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,esk2_2(X14,X15))
        | ~ r2_hidden(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_ordinal1(X1,esk5_1(X1))
    | ~ r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v3_ordinal1(esk5_1(X1))
    | ~ r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_1(X1),X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

fof(c_0_31,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ r1_tarski(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_32,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk5_1(esk2_2(X1,X2)),X2)
    | ~ r2_hidden(esk2_2(X1,X2),esk3_0)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_1(X1),esk3_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X5,X6] :
      ( ( ~ r2_hidden(esk1_2(X5,X6),X5)
        | ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_39,negated_conjecture,
    ( ~ v3_ordinal1(esk2_2(X1,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_35])).

cnf(c_0_43,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.36  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.14/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.36  #
% 0.14/0.36  # Preprocessing time       : 0.013 s
% 0.14/0.36  
% 0.14/0.36  # Proof found!
% 0.14/0.36  # SZS status Theorem
% 0.14/0.36  # SZS output start CNFRefutation
% 0.14/0.36  fof(t32_ordinal1, conjecture, ![X1, X2]:(v3_ordinal1(X2)=>~(((r1_tarski(X1,X2)&X1!=k1_xboole_0)&![X3]:(v3_ordinal1(X3)=>~((r2_hidden(X3,X1)&![X4]:(v3_ordinal1(X4)=>(r2_hidden(X4,X1)=>r1_ordinal1(X3,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_ordinal1)).
% 0.14/0.36  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.14/0.36  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.14/0.36  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.14/0.36  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.14/0.36  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 0.14/0.36  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.36  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.14/0.36  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(v3_ordinal1(X2)=>~(((r1_tarski(X1,X2)&X1!=k1_xboole_0)&![X3]:(v3_ordinal1(X3)=>~((r2_hidden(X3,X1)&![X4]:(v3_ordinal1(X4)=>(r2_hidden(X4,X1)=>r1_ordinal1(X3,X4)))))))))), inference(assume_negation,[status(cth)],[t32_ordinal1])).
% 0.14/0.36  fof(c_0_10, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.14/0.36  fof(c_0_11, negated_conjecture, ![X26]:(v3_ordinal1(esk4_0)&((r1_tarski(esk3_0,esk4_0)&esk3_0!=k1_xboole_0)&((v3_ordinal1(esk5_1(X26))|~r2_hidden(X26,esk3_0)|~v3_ordinal1(X26))&((r2_hidden(esk5_1(X26),esk3_0)|~r2_hidden(X26,esk3_0)|~v3_ordinal1(X26))&(~r1_ordinal1(X26,esk5_1(X26))|~r2_hidden(X26,esk3_0)|~v3_ordinal1(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).
% 0.14/0.36  fof(c_0_12, plain, ![X12, X13]:((~r1_tarski(k1_tarski(X12),X13)|r2_hidden(X12,X13))&(~r2_hidden(X12,X13)|r1_tarski(k1_tarski(X12),X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.14/0.36  cnf(c_0_13, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.36  cnf(c_0_14, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.36  cnf(c_0_16, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.36  fof(c_0_17, plain, ![X20, X21]:(~v3_ordinal1(X20)|(~v3_ordinal1(X21)|(r1_ordinal1(X20,X21)|r2_hidden(X21,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.14/0.36  fof(c_0_18, plain, ![X18, X19]:(~v3_ordinal1(X19)|(~r2_hidden(X18,X19)|v3_ordinal1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.14/0.36  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,esk4_0)|~r1_tarski(k1_tarski(X1),esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.36  cnf(c_0_20, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.36  fof(c_0_21, plain, ![X14, X15, X17]:((r2_hidden(esk2_2(X14,X15),X15)|~r2_hidden(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,esk2_2(X14,X15))|~r2_hidden(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.14/0.36  cnf(c_0_22, negated_conjecture, (~r1_ordinal1(X1,esk5_1(X1))|~r2_hidden(X1,esk3_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_23, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.36  cnf(c_0_24, negated_conjecture, (v3_ordinal1(esk5_1(X1))|~r2_hidden(X1,esk3_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_25, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.36  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.36  cnf(c_0_27, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk2_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.36  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_1(X1),X1)|~v3_ordinal1(X1)|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.14/0.36  cnf(c_0_30, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.14/0.36  fof(c_0_31, plain, ![X22, X23]:(~r2_hidden(X22,X23)|~r1_tarski(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.36  fof(c_0_32, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.36  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk5_1(esk2_2(X1,X2)),X2)|~r2_hidden(esk2_2(X1,X2),esk3_0)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.14/0.36  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_1(X1),esk3_0)|~r2_hidden(X1,esk3_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.36  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.36  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.36  fof(c_0_38, plain, ![X5, X6]:((~r2_hidden(esk1_2(X5,X6),X5)|~r2_hidden(esk1_2(X5,X6),X6)|X5=X6)&(r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(esk1_2(X5,X6),X6)|X5=X6)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.14/0.36  cnf(c_0_39, negated_conjecture, (~v3_ordinal1(esk2_2(X1,esk3_0))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.14/0.36  cnf(c_0_40, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.36  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.36  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_30]), c_0_35])).
% 0.14/0.36  cnf(c_0_43, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.36  cnf(c_0_44, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['proof']).
% 0.14/0.36  # SZS output end CNFRefutation
% 0.14/0.36  # Proof object total steps             : 46
% 0.14/0.36  # Proof object clause steps            : 27
% 0.14/0.36  # Proof object formula steps           : 19
% 0.14/0.36  # Proof object conjectures             : 18
% 0.14/0.36  # Proof object clause conjectures      : 15
% 0.14/0.36  # Proof object formula conjectures     : 3
% 0.14/0.36  # Proof object initial clauses used    : 16
% 0.14/0.36  # Proof object initial formulas used   : 9
% 0.14/0.36  # Proof object generating inferences   : 11
% 0.14/0.36  # Proof object simplifying inferences  : 7
% 0.14/0.36  # Training examples: 0 positive, 0 negative
% 0.14/0.36  # Parsed axioms                        : 9
% 0.14/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.36  # Initial clauses                      : 17
% 0.14/0.36  # Removed in clause preprocessing      : 0
% 0.14/0.36  # Initial clauses in saturation        : 17
% 0.14/0.36  # Processed clauses                    : 56
% 0.14/0.36  # ...of these trivial                  : 0
% 0.14/0.36  # ...subsumed                          : 7
% 0.14/0.36  # ...remaining for further processing  : 49
% 0.14/0.36  # Other redundant clauses eliminated   : 0
% 0.14/0.36  # Clauses deleted for lack of memory   : 0
% 0.14/0.36  # Backward-subsumed                    : 0
% 0.14/0.36  # Backward-rewritten                   : 0
% 0.14/0.36  # Generated clauses                    : 87
% 0.14/0.36  # ...of the previous two non-trivial   : 78
% 0.14/0.36  # Contextual simplify-reflections      : 5
% 0.14/0.36  # Paramodulations                      : 85
% 0.14/0.36  # Factorizations                       : 2
% 0.14/0.36  # Equation resolutions                 : 0
% 0.14/0.36  # Propositional unsat checks           : 0
% 0.14/0.36  #    Propositional check models        : 0
% 0.14/0.36  #    Propositional check unsatisfiable : 0
% 0.14/0.36  #    Propositional clauses             : 0
% 0.14/0.36  #    Propositional clauses after purity: 0
% 0.14/0.36  #    Propositional unsat core size     : 0
% 0.14/0.36  #    Propositional preprocessing time  : 0.000
% 0.14/0.36  #    Propositional encoding time       : 0.000
% 0.14/0.36  #    Propositional solver time         : 0.000
% 0.14/0.36  #    Success case prop preproc time    : 0.000
% 0.14/0.36  #    Success case prop encoding time   : 0.000
% 0.14/0.36  #    Success case prop solver time     : 0.000
% 0.14/0.36  # Current number of processed clauses  : 49
% 0.14/0.36  #    Positive orientable unit clauses  : 3
% 0.14/0.36  #    Positive unorientable unit clauses: 0
% 0.14/0.36  #    Negative unit clauses             : 5
% 0.14/0.36  #    Non-unit-clauses                  : 41
% 0.14/0.36  # Current number of unprocessed clauses: 36
% 0.14/0.36  # ...number of literals in the above   : 144
% 0.14/0.36  # Current number of archived formulas  : 0
% 0.14/0.36  # Current number of archived clauses   : 0
% 0.14/0.36  # Clause-clause subsumption calls (NU) : 215
% 0.14/0.36  # Rec. Clause-clause subsumption calls : 110
% 0.14/0.36  # Non-unit clause-clause subsumptions  : 8
% 0.14/0.36  # Unit Clause-clause subsumption calls : 31
% 0.14/0.36  # Rewrite failures with RHS unbound    : 0
% 0.14/0.36  # BW rewrite match attempts            : 0
% 0.14/0.36  # BW rewrite match successes           : 0
% 0.14/0.36  # Condensation attempts                : 0
% 0.14/0.36  # Condensation successes               : 0
% 0.14/0.36  # Termbank termtop insertions          : 2298
% 0.14/0.36  
% 0.14/0.36  # -------------------------------------------------
% 0.14/0.36  # User time                : 0.015 s
% 0.14/0.36  # System time              : 0.002 s
% 0.14/0.36  # Total time               : 0.017 s
% 0.14/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:56:14 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of clauses        :   28 (  43 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  156 ( 540 expanded)
%              Number of equality atoms :    9 (  36 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t3_ordinal1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & r2_hidden(X2,X3)
        & r2_hidden(X3,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

fof(t136_zfmisc_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( r2_hidden(X1,X2)
      & ! [X3,X4] :
          ( ( r2_hidden(X3,X2)
            & r1_tarski(X4,X3) )
         => r2_hidden(X4,X2) )
      & ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(k1_zfmisc_1(X3),X2) )
      & ! [X3] :
          ~ ( r1_tarski(X3,X2)
            & ~ r2_tarski(X3,X2)
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X33] :
      ( v3_ordinal1(esk6_0)
      & r1_tarski(esk5_0,esk6_0)
      & esk5_0 != k1_xboole_0
      & ( v3_ordinal1(esk7_1(X33))
        | ~ r2_hidden(X33,esk5_0)
        | ~ v3_ordinal1(X33) )
      & ( r2_hidden(esk7_1(X33),esk5_0)
        | ~ r2_hidden(X33,esk5_0)
        | ~ v3_ordinal1(X33) )
      & ( ~ r1_ordinal1(X33,esk7_1(X33))
        | ~ r2_hidden(X33,esk5_0)
        | ~ v3_ordinal1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X25)
      | ~ r2_hidden(X24,X25)
      | v3_ordinal1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X26,X27] :
      ( ~ v3_ordinal1(X26)
      | ~ v3_ordinal1(X27)
      | r1_ordinal1(X26,X27)
      | r2_hidden(X27,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_15,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_ordinal1(X1,esk7_1(X1))
    | ~ r2_hidden(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ r2_hidden(X29,X30)
      | ~ r2_hidden(X30,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_ordinal1])])).

fof(c_0_22,plain,(
    ! [X11,X13,X14,X15,X16] :
      ( r2_hidden(X11,esk2_1(X11))
      & ( ~ r2_hidden(X13,esk2_1(X11))
        | ~ r1_tarski(X14,X13)
        | r2_hidden(X14,esk2_1(X11)) )
      & ( ~ r2_hidden(X15,esk2_1(X11))
        | r2_hidden(k1_zfmisc_1(X15),esk2_1(X11)) )
      & ( ~ r1_tarski(X16,esk2_1(X11))
        | r2_tarski(X16,esk2_1(X11))
        | r2_hidden(X16,esk2_1(X11)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t136_zfmisc_1])])])])])).

fof(c_0_23,plain,(
    ! [X17,X18,X20] :
      ( ( r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(X17,X18) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,esk3_2(X17,X18))
        | ~ r2_hidden(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk7_1(X1),X1)
    | ~ v3_ordinal1(esk7_1(X1))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk7_1(X1))
    | ~ r2_hidden(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk3_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk7_1(X1),X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(esk2_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,esk2_1(X2))
    | ~ r2_hidden(X1,esk2_1(X2))
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk7_1(esk3_2(X1,X2)),X2)
    | ~ r2_hidden(esk3_2(X1,X2),esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk7_1(X1),esk5_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(esk2_1(esk2_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,esk2_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

fof(c_0_37,plain,(
    ! [X21,X22] :
      ( ( r2_hidden(esk4_2(X21,X22),X21)
        | X21 = k1_xboole_0
        | r1_tarski(X22,k1_setfam_1(X21)) )
      & ( ~ r1_tarski(X22,esk4_2(X21,X22))
        | X21 = k1_xboole_0
        | r1_tarski(X22,k1_setfam_1(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v3_ordinal1(esk3_2(X1,esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_39,plain,
    ( ~ r1_tarski(esk2_1(esk2_1(esk2_1(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_20]),c_0_34])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(X1,esk2_1(esk2_1(esk2_1(k1_setfam_1(X1))))),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:17:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.028 s
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t32_ordinal1, conjecture, ![X1, X2]:(v3_ordinal1(X2)=>~(((r1_tarski(X1,X2)&X1!=k1_xboole_0)&![X3]:(v3_ordinal1(X3)=>~((r2_hidden(X3,X1)&![X4]:(v3_ordinal1(X4)=>(r2_hidden(X4,X1)=>r1_ordinal1(X3,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_ordinal1)).
% 0.19/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.40  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.19/0.40  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.19/0.40  fof(t3_ordinal1, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&r2_hidden(X2,X3))&r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_ordinal1)).
% 0.19/0.40  fof(t136_zfmisc_1, axiom, ![X1]:?[X2]:(((r2_hidden(X1,X2)&![X3, X4]:((r2_hidden(X3,X2)&r1_tarski(X4,X3))=>r2_hidden(X4,X2)))&![X3]:(r2_hidden(X3,X2)=>r2_hidden(k1_zfmisc_1(X3),X2)))&![X3]:~(((r1_tarski(X3,X2)&~(r2_tarski(X3,X2)))&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 0.19/0.40  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 0.19/0.40  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.19/0.40  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(v3_ordinal1(X2)=>~(((r1_tarski(X1,X2)&X1!=k1_xboole_0)&![X3]:(v3_ordinal1(X3)=>~((r2_hidden(X3,X1)&![X4]:(v3_ordinal1(X4)=>(r2_hidden(X4,X1)=>r1_ordinal1(X3,X4)))))))))), inference(assume_negation,[status(cth)],[t32_ordinal1])).
% 0.19/0.40  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.40  fof(c_0_10, negated_conjecture, ![X33]:(v3_ordinal1(esk6_0)&((r1_tarski(esk5_0,esk6_0)&esk5_0!=k1_xboole_0)&((v3_ordinal1(esk7_1(X33))|~r2_hidden(X33,esk5_0)|~v3_ordinal1(X33))&((r2_hidden(esk7_1(X33),esk5_0)|~r2_hidden(X33,esk5_0)|~v3_ordinal1(X33))&(~r1_ordinal1(X33,esk7_1(X33))|~r2_hidden(X33,esk5_0)|~v3_ordinal1(X33)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).
% 0.19/0.40  fof(c_0_11, plain, ![X24, X25]:(~v3_ordinal1(X25)|(~r2_hidden(X24,X25)|v3_ordinal1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.19/0.40  cnf(c_0_12, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_13, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_14, plain, ![X26, X27]:(~v3_ordinal1(X26)|(~v3_ordinal1(X27)|(r1_ordinal1(X26,X27)|r2_hidden(X27,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.19/0.40  cnf(c_0_15, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (v3_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (~r1_ordinal1(X1,esk7_1(X1))|~r2_hidden(X1,esk5_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_19, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.19/0.40  fof(c_0_21, plain, ![X28, X29, X30]:(~r2_hidden(X28,X29)|~r2_hidden(X29,X30)|~r2_hidden(X30,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_ordinal1])])).
% 0.19/0.40  fof(c_0_22, plain, ![X11, X13, X14, X15, X16]:(((r2_hidden(X11,esk2_1(X11))&(~r2_hidden(X13,esk2_1(X11))|~r1_tarski(X14,X13)|r2_hidden(X14,esk2_1(X11))))&(~r2_hidden(X15,esk2_1(X11))|r2_hidden(k1_zfmisc_1(X15),esk2_1(X11))))&(~r1_tarski(X16,esk2_1(X11))|r2_tarski(X16,esk2_1(X11))|r2_hidden(X16,esk2_1(X11)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t136_zfmisc_1])])])])])).
% 0.19/0.40  fof(c_0_23, plain, ![X17, X18, X20]:((r2_hidden(esk3_2(X17,X18),X18)|~r2_hidden(X17,X18))&(~r2_hidden(X20,X18)|~r2_hidden(X20,esk3_2(X17,X18))|~r2_hidden(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (r2_hidden(esk7_1(X1),X1)|~v3_ordinal1(esk7_1(X1))|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk7_1(X1))|~r2_hidden(X1,esk5_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_27, plain, (r2_hidden(X1,esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk3_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(esk7_1(X1),X1)|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20])).
% 0.19/0.40  cnf(c_0_30, plain, (~r2_hidden(esk2_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  cnf(c_0_31, plain, (r2_hidden(X3,esk2_1(X2))|~r2_hidden(X1,esk2_1(X2))|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk7_1(esk3_2(X1,X2)),X2)|~r2_hidden(esk3_2(X1,X2),esk5_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (r2_hidden(esk7_1(X1),esk5_0)|~r2_hidden(X1,esk5_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_34, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_35, plain, (~r2_hidden(esk2_1(esk2_1(X1)),X1)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.19/0.40  cnf(c_0_36, plain, (r2_hidden(X1,esk2_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.19/0.40  fof(c_0_37, plain, ![X21, X22]:((r2_hidden(esk4_2(X21,X22),X21)|(X21=k1_xboole_0|r1_tarski(X22,k1_setfam_1(X21))))&(~r1_tarski(X22,esk4_2(X21,X22))|(X21=k1_xboole_0|r1_tarski(X22,k1_setfam_1(X21))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (~v3_ordinal1(esk3_2(X1,esk5_0))|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.19/0.40  cnf(c_0_39, plain, (~r1_tarski(esk2_1(esk2_1(esk2_1(X1))),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.40  cnf(c_0_40, plain, (r2_hidden(esk4_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_20]), c_0_34])).
% 0.19/0.40  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(X1,esk2_1(esk2_1(esk2_1(k1_setfam_1(X1))))),X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 45
% 0.19/0.40  # Proof object clause steps            : 28
% 0.19/0.40  # Proof object formula steps           : 17
% 0.19/0.40  # Proof object conjectures             : 17
% 0.19/0.40  # Proof object clause conjectures      : 14
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 15
% 0.19/0.40  # Proof object initial formulas used   : 8
% 0.19/0.40  # Proof object generating inferences   : 13
% 0.19/0.40  # Proof object simplifying inferences  : 7
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 8
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 20
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 20
% 0.19/0.40  # Processed clauses                    : 225
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 34
% 0.19/0.40  # ...remaining for further processing  : 191
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 7
% 0.19/0.40  # Backward-rewritten                   : 0
% 0.19/0.40  # Generated clauses                    : 1056
% 0.19/0.40  # ...of the previous two non-trivial   : 1045
% 0.19/0.40  # Contextual simplify-reflections      : 12
% 0.19/0.40  # Paramodulations                      : 1056
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
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
% 0.19/0.40  # Current number of processed clauses  : 184
% 0.19/0.40  #    Positive orientable unit clauses  : 4
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 5
% 0.19/0.40  #    Non-unit-clauses                  : 175
% 0.19/0.40  # Current number of unprocessed clauses: 837
% 0.19/0.40  # ...number of literals in the above   : 4063
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 7
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 2599
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1254
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 48
% 0.19/0.40  # Unit Clause-clause subsumption calls : 81
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 3
% 0.19/0.40  # BW rewrite match successes           : 0
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 19888
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.058 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.064 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

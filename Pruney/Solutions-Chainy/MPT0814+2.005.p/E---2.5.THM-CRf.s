%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:01 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 116 expanded)
%              Number of clauses        :   31 (  50 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 432 expanded)
%              Number of equality atoms :   23 (  68 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t65_subset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X4,X3)
        & r1_tarski(X3,k2_zfmisc_1(X1,X2))
        & ! [X5] :
            ( m1_subset_1(X5,X1)
           => ! [X6] :
                ( m1_subset_1(X6,X2)
               => X4 != k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
       => ~ ( r2_hidden(X1,X4)
            & ! [X5,X6] :
                ~ ( X1 = k4_tarski(X5,X6)
                  & r2_hidden(X5,X2)
                  & r2_hidden(X6,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_relset_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X17,X18,X19,X20,X21,X22,X24,X25] :
      ( ( r2_hidden(esk2_4(X11,X12,X13,X14),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( r2_hidden(esk3_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( X14 = k4_tarski(esk2_4(X11,X12,X13,X14),esk3_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( ~ r2_hidden(X18,X11)
        | ~ r2_hidden(X19,X12)
        | X17 != k4_tarski(X18,X19)
        | r2_hidden(X17,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( ~ r2_hidden(esk4_3(X20,X21,X22),X22)
        | ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X25,X21)
        | esk4_3(X20,X21,X22) != k4_tarski(X24,X25)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk5_3(X20,X21,X22),X20)
        | r2_hidden(esk4_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk6_3(X20,X21,X22),X21)
        | r2_hidden(esk4_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( esk4_3(X20,X21,X22) = k4_tarski(esk5_3(X20,X21,X22),esk6_3(X20,X21,X22))
        | r2_hidden(esk4_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X44,X45] :
      ( m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0)))
      & r2_hidden(esk9_0,esk12_0)
      & ( esk9_0 != k4_tarski(X44,X45)
        | ~ r2_hidden(X44,esk10_0)
        | ~ r2_hidden(X45,esk11_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X34,X35] :
      ( ~ v1_xboole_0(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(X34))
      | v1_xboole_0(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_13,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk9_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X36,X37)
      | v1_xboole_0(X37)
      | r2_hidden(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_18,plain,(
    ! [X28,X29,X30,X31] :
      ( ( m1_subset_1(esk7_4(X28,X29,X30,X31),X28)
        | ~ r2_hidden(X31,X30)
        | ~ r1_tarski(X30,k2_zfmisc_1(X28,X29)) )
      & ( m1_subset_1(esk8_4(X28,X29,X30,X31),X29)
        | ~ r2_hidden(X31,X30)
        | ~ r1_tarski(X30,k2_zfmisc_1(X28,X29)) )
      & ( X31 = k4_tarski(esk7_4(X28,X29,X30,X31),esk8_4(X28,X29,X30,X31))
        | ~ r2_hidden(X31,X30)
        | ~ r1_tarski(X30,k2_zfmisc_1(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_subset_1])])])])).

fof(c_0_19,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk12_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk8_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( esk9_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X2,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( X1 = k4_tarski(esk7_4(X2,X3,X4,X1),esk8_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(X4,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( r2_hidden(esk8_4(X1,X2,X3,X4),X2)
    | v1_xboole_0(X2)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk12_0,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk11_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk7_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk8_4(X2,X3,X1,esk9_0),esk11_0)
    | ~ r2_hidden(esk7_4(X2,X3,X1,esk9_0),esk10_0)
    | ~ r2_hidden(esk9_0,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk8_4(esk10_0,esk11_0,esk12_0,X1),esk11_0)
    | ~ r2_hidden(X1,esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X1)
    | v1_xboole_0(X1)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk10_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk7_4(esk10_0,esk11_0,esk12_0,esk9_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_35]),c_0_14])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_4(esk10_0,esk11_0,esk12_0,X1),esk10_0)
    | ~ r2_hidden(X1,esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t6_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 0.20/0.39  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.20/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.39  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.39  fof(t65_subset_1, axiom, ![X1, X2, X3, X4]:~(((r2_hidden(X4,X3)&r1_tarski(X3,k2_zfmisc_1(X1,X2)))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>X4!=k4_tarski(X5,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 0.20/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3))))))), inference(assume_negation,[status(cth)],[t6_relset_1])).
% 0.20/0.39  fof(c_0_8, plain, ![X11, X12, X13, X14, X17, X18, X19, X20, X21, X22, X24, X25]:(((((r2_hidden(esk2_4(X11,X12,X13,X14),X11)|~r2_hidden(X14,X13)|X13!=k2_zfmisc_1(X11,X12))&(r2_hidden(esk3_4(X11,X12,X13,X14),X12)|~r2_hidden(X14,X13)|X13!=k2_zfmisc_1(X11,X12)))&(X14=k4_tarski(esk2_4(X11,X12,X13,X14),esk3_4(X11,X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k2_zfmisc_1(X11,X12)))&(~r2_hidden(X18,X11)|~r2_hidden(X19,X12)|X17!=k4_tarski(X18,X19)|r2_hidden(X17,X13)|X13!=k2_zfmisc_1(X11,X12)))&((~r2_hidden(esk4_3(X20,X21,X22),X22)|(~r2_hidden(X24,X20)|~r2_hidden(X25,X21)|esk4_3(X20,X21,X22)!=k4_tarski(X24,X25))|X22=k2_zfmisc_1(X20,X21))&(((r2_hidden(esk5_3(X20,X21,X22),X20)|r2_hidden(esk4_3(X20,X21,X22),X22)|X22=k2_zfmisc_1(X20,X21))&(r2_hidden(esk6_3(X20,X21,X22),X21)|r2_hidden(esk4_3(X20,X21,X22),X22)|X22=k2_zfmisc_1(X20,X21)))&(esk4_3(X20,X21,X22)=k4_tarski(esk5_3(X20,X21,X22),esk6_3(X20,X21,X22))|r2_hidden(esk4_3(X20,X21,X22),X22)|X22=k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.20/0.39  fof(c_0_9, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.39  fof(c_0_10, negated_conjecture, ![X44, X45]:(m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0)))&(r2_hidden(esk9_0,esk12_0)&(esk9_0!=k4_tarski(X44,X45)|~r2_hidden(X44,esk10_0)|~r2_hidden(X45,esk11_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.20/0.39  cnf(c_0_11, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  fof(c_0_12, plain, ![X34, X35]:(~v1_xboole_0(X34)|(~m1_subset_1(X35,k1_zfmisc_1(X34))|v1_xboole_0(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.39  cnf(c_0_13, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (r2_hidden(esk9_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_15, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_16, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  fof(c_0_17, plain, ![X36, X37]:(~m1_subset_1(X36,X37)|(v1_xboole_0(X37)|r2_hidden(X36,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.39  fof(c_0_18, plain, ![X28, X29, X30, X31]:((m1_subset_1(esk7_4(X28,X29,X30,X31),X28)|(~r2_hidden(X31,X30)|~r1_tarski(X30,k2_zfmisc_1(X28,X29))))&((m1_subset_1(esk8_4(X28,X29,X30,X31),X29)|(~r2_hidden(X31,X30)|~r1_tarski(X30,k2_zfmisc_1(X28,X29))))&(X31=k4_tarski(esk7_4(X28,X29,X30,X31),esk8_4(X28,X29,X30,X31))|(~r2_hidden(X31,X30)|~r1_tarski(X30,k2_zfmisc_1(X28,X29)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_subset_1])])])])).
% 0.20/0.39  fof(c_0_19, plain, ![X38, X39]:((~m1_subset_1(X38,k1_zfmisc_1(X39))|r1_tarski(X38,X39))&(~r1_tarski(X38,X39)|m1_subset_1(X38,k1_zfmisc_1(X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.39  cnf(c_0_20, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (~v1_xboole_0(esk12_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.39  cnf(c_0_23, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_13, c_0_15])).
% 0.20/0.39  cnf(c_0_24, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_25, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_26, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_27, plain, (m1_subset_1(esk8_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk10_0,esk11_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.39  cnf(c_0_30, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.39  cnf(c_0_31, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_13, c_0_25])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (esk9_0!=k4_tarski(X1,X2)|~r2_hidden(X1,esk10_0)|~r2_hidden(X2,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_33, plain, (X1=k4_tarski(esk7_4(X2,X3,X4,X1),esk8_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|~r1_tarski(X4,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_34, plain, (r2_hidden(esk8_4(X1,X2,X3,X4),X2)|v1_xboole_0(X2)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (r1_tarski(esk12_0,k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (~v1_xboole_0(esk11_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.39  cnf(c_0_37, plain, (m1_subset_1(esk7_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_38, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(esk8_4(X2,X3,X1,esk9_0),esk11_0)|~r2_hidden(esk7_4(X2,X3,X1,esk9_0),esk10_0)|~r2_hidden(esk9_0,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33])])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(esk8_4(esk10_0,esk11_0,esk12_0,X1),esk11_0)|~r2_hidden(X1,esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.20/0.39  cnf(c_0_41, plain, (r2_hidden(esk7_4(X1,X2,X3,X4),X1)|v1_xboole_0(X1)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_26, c_0_37])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(esk10_0)), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk7_4(esk10_0,esk11_0,esk12_0,esk9_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_35]), c_0_14])])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk7_4(esk10_0,esk11_0,esk12_0,X1),esk10_0)|~r2_hidden(X1,esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_42])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_14])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 46
% 0.20/0.39  # Proof object clause steps            : 31
% 0.20/0.39  # Proof object formula steps           : 15
% 0.20/0.39  # Proof object conjectures             : 16
% 0.20/0.39  # Proof object clause conjectures      : 13
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 13
% 0.20/0.39  # Proof object initial formulas used   : 7
% 0.20/0.39  # Proof object generating inferences   : 16
% 0.20/0.39  # Proof object simplifying inferences  : 11
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 7
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 20
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 20
% 0.20/0.39  # Processed clauses                    : 217
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 70
% 0.20/0.39  # ...remaining for further processing  : 147
% 0.20/0.39  # Other redundant clauses eliminated   : 7
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 688
% 0.20/0.39  # ...of the previous two non-trivial   : 683
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 682
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 7
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 123
% 0.20/0.39  #    Positive orientable unit clauses  : 3
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 5
% 0.20/0.39  #    Non-unit-clauses                  : 115
% 0.20/0.39  # Current number of unprocessed clauses: 506
% 0.20/0.39  # ...number of literals in the above   : 1526
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 20
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2804
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 2312
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 64
% 0.20/0.39  # Unit Clause-clause subsumption calls : 69
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 11752
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.044 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.048 s
% 0.20/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

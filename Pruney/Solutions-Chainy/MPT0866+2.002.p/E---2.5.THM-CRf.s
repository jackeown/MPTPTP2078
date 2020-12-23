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
% DateTime   : Thu Dec  3 10:59:30 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 (  74 expanded)
%              Number of clauses        :   29 (  35 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 298 expanded)
%              Number of equality atoms :   87 ( 185 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(t24_mcart_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(t55_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X7
        | X10 = X8
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( esk1_3(X12,X13,X14) != X12
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( esk1_3(X12,X13,X14) != X13
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | esk1_3(X12,X13,X14) = X12
        | esk1_3(X12,X13,X14) = X13
        | X14 = k2_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ r2_hidden(X35,X36)
      | X35 = k4_tarski(k1_mcart_1(X35),k2_mcart_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_10,plain,(
    ! [X21,X22,X25,X27,X28] :
      ( ( ~ v1_relat_1(X21)
        | ~ r2_hidden(X22,X21)
        | X22 = k4_tarski(esk2_2(X21,X22),esk3_2(X21,X22)) )
      & ( r2_hidden(esk4_1(X25),X25)
        | v1_relat_1(X25) )
      & ( esk4_1(X25) != k4_tarski(X27,X28)
        | v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ! [X3] :
                ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
               => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t24_mcart_1])).

cnf(c_0_15,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | r2_hidden(esk4_1(X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,X19)
      | X19 = k1_xboole_0
      | m1_subset_1(k1_tarski(X20),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).

fof(c_0_19,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & m1_subset_1(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))
    & esk9_0 != k4_tarski(k1_mcart_1(esk9_0),k2_mcart_1(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_21,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | esk4_1(k2_tarski(X2,X3)) = X3
    | esk4_1(k2_tarski(X2,X3)) = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).

fof(c_0_23,plain,(
    ! [X29,X30,X31,X32] :
      ( ( X29 = k4_tarski(esk5_4(X29,X30,X31,X32),esk6_4(X29,X30,X31,X32))
        | ~ r2_hidden(X29,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( r2_hidden(esk5_4(X29,X30,X31,X32),X30)
        | ~ r2_hidden(X29,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( r2_hidden(esk6_4(X29,X30,X31,X32),X31)
        | ~ r2_hidden(X29,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).

cnf(c_0_24,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( esk9_0 != k4_tarski(k1_mcart_1(esk9_0),k2_mcart_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | esk4_1(k2_tarski(X1,X2)) = X1
    | esk4_1(k2_tarski(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( X1 = k4_tarski(esk5_4(X1,X2,X3,X4),esk6_4(X1,X2,X3,X4))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( esk4_1(k2_tarski(esk9_0,X1)) = esk9_0
    | esk4_1(k2_tarski(esk9_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k4_tarski(esk5_4(X1,X2,X3,k2_tarski(X4,X4)),esk6_4(X1,X2,X3,k2_tarski(X4,X4))) = X1
    | k2_zfmisc_1(X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X1,k2_tarski(X4,X4)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk9_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | esk4_1(X1) != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( esk4_1(k2_tarski(esk9_0,esk9_0)) = esk9_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( k4_tarski(esk5_4(X1,esk7_0,esk8_0,k2_tarski(esk9_0,esk9_0)),esk6_4(X1,esk7_0,esk8_0,k2_tarski(esk9_0,esk9_0))) = X1
    | k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | ~ r2_hidden(X1,k2_tarski(esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k2_tarski(esk9_0,esk9_0))
    | k4_tarski(X1,X2) != esk9_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(esk5_4(esk9_0,esk7_0,esk8_0,k2_tarski(esk9_0,esk9_0)),esk6_4(esk9_0,esk7_0,esk8_0,k2_tarski(esk9_0,esk9_0))) = esk9_0
    | k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | v1_relat_1(k2_tarski(esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_39,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | ~ r2_hidden(X1,k2_tarski(esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_38])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_22]),c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:47:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.18/0.37  # and selection function SelectCQIArNXTEqFirst.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.028 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.18/0.37  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.18/0.37  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.18/0.37  fof(t24_mcart_1, conjecture, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 0.18/0.37  fof(t55_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 0.18/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.37  fof(t6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 0.18/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.37  fof(c_0_8, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(X10=X7|X10=X8)|X9!=k2_tarski(X7,X8))&((X11!=X7|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))))&(((esk1_3(X12,X13,X14)!=X12|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13))&(esk1_3(X12,X13,X14)!=X13|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(esk1_3(X12,X13,X14)=X12|esk1_3(X12,X13,X14)=X13)|X14=k2_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.18/0.37  fof(c_0_9, plain, ![X35, X36]:(~v1_relat_1(X36)|(~r2_hidden(X35,X36)|X35=k4_tarski(k1_mcart_1(X35),k2_mcart_1(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.18/0.37  fof(c_0_10, plain, ![X21, X22, X25, X27, X28]:((~v1_relat_1(X21)|(~r2_hidden(X22,X21)|X22=k4_tarski(esk2_2(X21,X22),esk3_2(X21,X22))))&((r2_hidden(esk4_1(X25),X25)|v1_relat_1(X25))&(esk4_1(X25)!=k4_tarski(X27,X28)|v1_relat_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.18/0.37  cnf(c_0_11, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  cnf(c_0_12, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_13, plain, (r2_hidden(esk4_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  fof(c_0_14, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3))))))), inference(assume_negation,[status(cth)],[t24_mcart_1])).
% 0.18/0.37  cnf(c_0_15, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_16, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|r2_hidden(esk4_1(X2),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.37  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  fof(c_0_18, plain, ![X19, X20]:(~m1_subset_1(X20,X19)|(X19=k1_xboole_0|m1_subset_1(k1_tarski(X20),k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).
% 0.18/0.37  fof(c_0_19, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.37  fof(c_0_20, negated_conjecture, ((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&(m1_subset_1(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))&esk9_0!=k4_tarski(k1_mcart_1(esk9_0),k2_mcart_1(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.18/0.37  cnf(c_0_21, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|esk4_1(k2_tarski(X2,X3))=X3|esk4_1(k2_tarski(X2,X3))=X2|~r2_hidden(X1,k2_tarski(X2,X3))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.37  cnf(c_0_22, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).
% 0.18/0.37  fof(c_0_23, plain, ![X29, X30, X31, X32]:(((X29=k4_tarski(esk5_4(X29,X30,X31,X32),esk6_4(X29,X30,X31,X32))|~r2_hidden(X29,X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(r2_hidden(esk5_4(X29,X30,X31,X32),X30)|~r2_hidden(X29,X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(r2_hidden(esk6_4(X29,X30,X31,X32),X31)|~r2_hidden(X29,X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).
% 0.18/0.37  cnf(c_0_24, plain, (X2=k1_xboole_0|m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.37  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.37  cnf(c_0_26, negated_conjecture, (esk9_0!=k4_tarski(k1_mcart_1(esk9_0),k2_mcart_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_27, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|esk4_1(k2_tarski(X1,X2))=X1|esk4_1(k2_tarski(X1,X2))=X2), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.37  cnf(c_0_28, plain, (X1=k4_tarski(esk5_4(X1,X2,X3,X4),esk6_4(X1,X2,X3,X4))|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.37  cnf(c_0_29, plain, (X2=k1_xboole_0|m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (esk4_1(k2_tarski(esk9_0,X1))=esk9_0|esk4_1(k2_tarski(esk9_0,X1))=X1), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.37  cnf(c_0_31, plain, (k4_tarski(esk5_4(X1,X2,X3,k2_tarski(X4,X4)),esk6_4(X1,X2,X3,k2_tarski(X4,X4)))=X1|k2_zfmisc_1(X2,X3)=k1_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(X2,X3))|~r2_hidden(X1,k2_tarski(X4,X4))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk9_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_33, plain, (v1_relat_1(X1)|esk4_1(X1)!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (esk4_1(k2_tarski(esk9_0,esk9_0))=esk9_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_30])])).
% 0.18/0.37  cnf(c_0_35, negated_conjecture, (k4_tarski(esk5_4(X1,esk7_0,esk8_0,k2_tarski(esk9_0,esk9_0)),esk6_4(X1,esk7_0,esk8_0,k2_tarski(esk9_0,esk9_0)))=X1|k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|~r2_hidden(X1,k2_tarski(esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.37  cnf(c_0_36, negated_conjecture, (v1_relat_1(k2_tarski(esk9_0,esk9_0))|k4_tarski(X1,X2)!=esk9_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.37  cnf(c_0_37, negated_conjecture, (k4_tarski(esk5_4(esk9_0,esk7_0,esk8_0,k2_tarski(esk9_0,esk9_0)),esk6_4(esk9_0,esk7_0,esk8_0,k2_tarski(esk9_0,esk9_0)))=esk9_0|k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_22])).
% 0.18/0.37  cnf(c_0_38, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|v1_relat_1(k2_tarski(esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.37  fof(c_0_39, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.37  cnf(c_0_40, negated_conjecture, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|~r2_hidden(X1,k2_tarski(esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_12, c_0_38])).
% 0.18/0.37  cnf(c_0_41, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_22]), c_0_26])).
% 0.18/0.37  cnf(c_0_43, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_44, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 46
% 0.18/0.37  # Proof object clause steps            : 29
% 0.18/0.37  # Proof object formula steps           : 17
% 0.18/0.37  # Proof object conjectures             : 16
% 0.18/0.37  # Proof object clause conjectures      : 13
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 13
% 0.18/0.37  # Proof object initial formulas used   : 8
% 0.18/0.37  # Proof object generating inferences   : 13
% 0.18/0.37  # Proof object simplifying inferences  : 8
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 8
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 22
% 0.18/0.37  # Removed in clause preprocessing      : 1
% 0.18/0.37  # Initial clauses in saturation        : 21
% 0.18/0.37  # Processed clauses                    : 102
% 0.18/0.37  # ...of these trivial                  : 1
% 0.18/0.37  # ...subsumed                          : 11
% 0.18/0.37  # ...remaining for further processing  : 90
% 0.18/0.37  # Other redundant clauses eliminated   : 53
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 1
% 0.18/0.37  # Backward-rewritten                   : 16
% 0.18/0.37  # Generated clauses                    : 255
% 0.18/0.37  # ...of the previous two non-trivial   : 154
% 0.18/0.37  # Contextual simplify-reflections      : 0
% 0.18/0.37  # Paramodulations                      : 180
% 0.18/0.37  # Factorizations                       : 24
% 0.18/0.37  # Equation resolutions                 : 53
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 47
% 0.18/0.37  #    Positive orientable unit clauses  : 7
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 3
% 0.18/0.37  #    Non-unit-clauses                  : 37
% 0.18/0.37  # Current number of unprocessed clauses: 86
% 0.18/0.37  # ...number of literals in the above   : 346
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 39
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 506
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 368
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 12
% 0.18/0.37  # Unit Clause-clause subsumption calls : 19
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 4
% 0.18/0.37  # BW rewrite match successes           : 2
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 5764
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.034 s
% 0.18/0.37  # System time              : 0.004 s
% 0.18/0.37  # Total time               : 0.038 s
% 0.18/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

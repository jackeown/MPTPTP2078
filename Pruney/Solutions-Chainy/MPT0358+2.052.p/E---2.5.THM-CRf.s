%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 346 expanded)
%              Number of clauses        :   40 ( 171 expanded)
%              Number of leaves         :   10 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  150 (1064 expanded)
%              Number of equality atoms :   45 ( 327 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

fof(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 != k1_subset_1(esk5_0) )
    & ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 = k1_subset_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_12,plain,(
    ! [X34] : k1_subset_1(X34) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_13,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X29,X28)
        | r1_tarski(X29,X27)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r1_tarski(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k1_zfmisc_1(X27) )
      & ( ~ r2_hidden(esk4_2(X31,X32),X32)
        | ~ r1_tarski(esk4_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) )
      & ( r2_hidden(esk4_2(X31,X32),X32)
        | r1_tarski(esk4_2(X31,X32),X31)
        | X32 = k1_zfmisc_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 != k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 = k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_20,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),k1_xboole_0)
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

fof(c_0_33,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23])).

fof(c_0_36,plain,(
    ! [X20] :
      ( X20 = k1_xboole_0
      | r2_hidden(esk3_1(X20),X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk6_0,k1_zfmisc_1(k3_subset_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_41,plain,(
    ! [X26] : k5_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(k3_subset_1(esk5_0,esk6_0)))
    | ~ r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(k3_subset_1(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_38])).

fof(c_0_48,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,X36) = k4_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | r2_hidden(esk3_1(X1),X1)
    | ~ r1_tarski(X1,k3_subset_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_47])).

cnf(c_0_51,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),k5_xboole_0(X1,k3_xboole_0(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0)) = k3_subset_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_52]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:46:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.20/0.41  # and selection function SelectCQIArEqFirst.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.20/0.41  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.20/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.41  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.41  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.41  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.20/0.41  fof(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&((~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0))&(r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.41  fof(c_0_12, plain, ![X34]:k1_subset_1(X34)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.20/0.41  fof(c_0_13, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X29,X28)|r1_tarski(X29,X27)|X28!=k1_zfmisc_1(X27))&(~r1_tarski(X30,X27)|r2_hidden(X30,X28)|X28!=k1_zfmisc_1(X27)))&((~r2_hidden(esk4_2(X31,X32),X32)|~r1_tarski(esk4_2(X31,X32),X31)|X32=k1_zfmisc_1(X31))&(r2_hidden(esk4_2(X31,X32),X32)|r1_tarski(esk4_2(X31,X32),X31)|X32=k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.41  cnf(c_0_14, negated_conjecture, (~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_15, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_17, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  fof(c_0_18, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.41  fof(c_0_19, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.41  fof(c_0_20, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (esk6_0!=k1_xboole_0|~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.20/0.41  cnf(c_0_23, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|~r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  cnf(c_0_28, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_31, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),k1_xboole_0)|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.20/0.41  fof(c_0_33, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.41  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_35, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23])).
% 0.20/0.41  fof(c_0_36, plain, ![X20]:(X20=k1_xboole_0|r2_hidden(esk3_1(X20),X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.41  cnf(c_0_37, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk6_0,k1_zfmisc_1(k3_subset_1(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 0.20/0.41  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.41  fof(c_0_41, plain, ![X26]:k5_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.41  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(k3_subset_1(esk5_0,esk6_0)))|~r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.41  cnf(c_0_44, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.41  cnf(c_0_45, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|~r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_21, c_0_42])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(k3_subset_1(esk5_0,esk6_0)))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_38])).
% 0.20/0.41  fof(c_0_48, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,X36)=k4_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|r2_hidden(esk3_1(X1),X1)|~r1_tarski(X1,k3_subset_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_46, c_0_42])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_47])).
% 0.20/0.41  cnf(c_0_51, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.41  cnf(c_0_53, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_51, c_0_26])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_55, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),k5_xboole_0(X1,k3_xboole_0(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_37, c_0_52])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0))=k3_subset_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_52]), c_0_59]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 61
% 0.20/0.41  # Proof object clause steps            : 40
% 0.20/0.41  # Proof object formula steps           : 21
% 0.20/0.41  # Proof object conjectures             : 22
% 0.20/0.41  # Proof object clause conjectures      : 19
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 15
% 0.20/0.41  # Proof object initial formulas used   : 10
% 0.20/0.41  # Proof object generating inferences   : 18
% 0.20/0.41  # Proof object simplifying inferences  : 11
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 10
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 22
% 0.20/0.41  # Removed in clause preprocessing      : 2
% 0.20/0.41  # Initial clauses in saturation        : 20
% 0.20/0.41  # Processed clauses                    : 205
% 0.20/0.41  # ...of these trivial                  : 3
% 0.20/0.41  # ...subsumed                          : 62
% 0.20/0.41  # ...remaining for further processing  : 140
% 0.20/0.41  # Other redundant clauses eliminated   : 9
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 11
% 0.20/0.41  # Backward-rewritten                   : 44
% 0.20/0.41  # Generated clauses                    : 1529
% 0.20/0.41  # ...of the previous two non-trivial   : 1457
% 0.20/0.41  # Contextual simplify-reflections      : 4
% 0.20/0.41  # Paramodulations                      : 1520
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 9
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 60
% 0.20/0.41  #    Positive orientable unit clauses  : 12
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 6
% 0.20/0.41  #    Non-unit-clauses                  : 42
% 0.20/0.41  # Current number of unprocessed clauses: 1285
% 0.20/0.41  # ...number of literals in the above   : 4920
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 77
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1054
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 642
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 72
% 0.20/0.41  # Unit Clause-clause subsumption calls : 146
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 38
% 0.20/0.41  # BW rewrite match successes           : 8
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 23729
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.050 s
% 0.20/0.41  # System time              : 0.008 s
% 0.20/0.41  # Total time               : 0.059 s
% 0.20/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:07 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 296 expanded)
%              Number of clauses        :   33 ( 123 expanded)
%              Number of leaves         :   10 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 (1051 expanded)
%              Number of equality atoms :   42 ( 224 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ~ ( X2 != k1_xboole_0
          & ! [X3] :
              ( m1_subset_1(X3,X1)
             => ~ r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t61_xboole_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ~ ( X2 != k1_xboole_0
            & ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_subset_1])).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( r2_hidden(X22,esk3_3(X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k3_tarski(X20) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_tarski(X20) )
      & ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X25,X20)
        | r2_hidden(X24,X21)
        | X21 != k3_tarski(X20) )
      & ( ~ r2_hidden(esk4_2(X26,X27),X27)
        | ~ r2_hidden(esk4_2(X26,X27),X29)
        | ~ r2_hidden(X29,X26)
        | X27 = k3_tarski(X26) )
      & ( r2_hidden(esk4_2(X26,X27),esk5_2(X26,X27))
        | r2_hidden(esk4_2(X26,X27),X27)
        | X27 = k3_tarski(X26) )
      & ( r2_hidden(esk5_2(X26,X27),X26)
        | r2_hidden(esk4_2(X26,X27),X27)
        | X27 = k3_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X33,X32)
        | r2_hidden(X33,X32)
        | v1_xboole_0(X32) )
      & ( ~ r2_hidden(X33,X32)
        | m1_subset_1(X33,X32)
        | v1_xboole_0(X32) )
      & ( ~ m1_subset_1(X33,X32)
        | v1_xboole_0(X33)
        | ~ v1_xboole_0(X32) )
      & ( ~ v1_xboole_0(X33)
        | m1_subset_1(X33,X32)
        | ~ v1_xboole_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_13,negated_conjecture,(
    ! [X36] :
      ( m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))
      & esk7_0 != k1_xboole_0
      & ( ~ m1_subset_1(X36,esk6_0)
        | ~ r2_hidden(X36,esk7_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X31] : k3_tarski(k1_zfmisc_1(X31)) = X31 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(esk6_0))
    | v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X8] :
      ( X8 = k1_xboole_0
      | r2_hidden(esk1_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_22,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | r1_tarski(X15,X13)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r1_tarski(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | ~ r1_tarski(esk2_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | r1_tarski(esk2_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | v1_xboole_0(k1_zfmisc_1(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk6_0)
    | v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ m1_subset_1(esk1_1(esk7_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_25])).

fof(c_0_32,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk6_0))
    | v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk6_0))
    | r1_tarski(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

fof(c_0_39,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = esk7_0
    | v1_xboole_0(k1_zfmisc_1(esk6_0))
    | ~ r1_tarski(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = esk7_0
    | v1_xboole_0(k1_zfmisc_1(esk6_0))
    | ~ r2_xboole_0(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_44]),c_0_25])).

fof(c_0_47,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_xboole_0(k1_xboole_0,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_xboole_1])])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ r2_xboole_0(k1_xboole_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46]),c_0_46]),c_0_25])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_52]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t10_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 0.20/0.38  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.20/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.38  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.20/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.38  fof(t61_xboole_1, axiom, ![X1]:(X1!=k1_xboole_0=>r2_xboole_0(k1_xboole_0,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 0.20/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2))))))), inference(assume_negation,[status(cth)],[t10_subset_1])).
% 0.20/0.38  fof(c_0_11, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:((((r2_hidden(X22,esk3_3(X20,X21,X22))|~r2_hidden(X22,X21)|X21!=k3_tarski(X20))&(r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(X22,X21)|X21!=k3_tarski(X20)))&(~r2_hidden(X24,X25)|~r2_hidden(X25,X20)|r2_hidden(X24,X21)|X21!=k3_tarski(X20)))&((~r2_hidden(esk4_2(X26,X27),X27)|(~r2_hidden(esk4_2(X26,X27),X29)|~r2_hidden(X29,X26))|X27=k3_tarski(X26))&((r2_hidden(esk4_2(X26,X27),esk5_2(X26,X27))|r2_hidden(esk4_2(X26,X27),X27)|X27=k3_tarski(X26))&(r2_hidden(esk5_2(X26,X27),X26)|r2_hidden(esk4_2(X26,X27),X27)|X27=k3_tarski(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.20/0.38  fof(c_0_12, plain, ![X32, X33]:(((~m1_subset_1(X33,X32)|r2_hidden(X33,X32)|v1_xboole_0(X32))&(~r2_hidden(X33,X32)|m1_subset_1(X33,X32)|v1_xboole_0(X32)))&((~m1_subset_1(X33,X32)|v1_xboole_0(X33)|~v1_xboole_0(X32))&(~v1_xboole_0(X33)|m1_subset_1(X33,X32)|~v1_xboole_0(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.38  fof(c_0_13, negated_conjecture, ![X36]:(m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))&(esk7_0!=k1_xboole_0&(~m1_subset_1(X36,esk6_0)|~r2_hidden(X36,esk7_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.20/0.38  cnf(c_0_14, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_15, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_17, plain, ![X31]:k3_tarski(k1_zfmisc_1(X31))=X31, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(esk6_0))|v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  cnf(c_0_20, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_21, plain, ![X8]:(X8=k1_xboole_0|r2_hidden(esk1_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.38  fof(c_0_22, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|r1_tarski(X15,X13)|X14!=k1_zfmisc_1(X13))&(~r1_tarski(X16,X13)|r2_hidden(X16,X14)|X14!=k1_zfmisc_1(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|~r1_tarski(esk2_2(X17,X18),X17)|X18=k1_zfmisc_1(X17))&(r2_hidden(esk2_2(X17,X18),X18)|r1_tarski(esk2_2(X17,X18),X17)|X18=k1_zfmisc_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk6_0)|v1_xboole_0(k1_zfmisc_1(esk6_0))|~r2_hidden(X1,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.20/0.38  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_28, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_1(esk7_0),esk6_0)|v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (~m1_subset_1(esk1_1(esk7_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_24]), c_0_25])).
% 0.20/0.38  fof(c_0_32, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.38  fof(c_0_34, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(k1_zfmisc_1(esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_16])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk6_0))|v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.20/0.38  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk6_0))|r1_tarski(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_19])).
% 0.20/0.38  fof(c_0_39, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.38  cnf(c_0_40, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (v1_xboole_0(esk6_0)|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (esk6_0=esk7_0|v1_xboole_0(k1_zfmisc_1(esk6_0))|~r1_tarski(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.38  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (esk6_0=k1_xboole_0|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (esk6_0=esk7_0|v1_xboole_0(k1_zfmisc_1(esk6_0))|~r2_xboole_0(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_44]), c_0_25])).
% 0.20/0.38  fof(c_0_47, plain, ![X12]:(X12=k1_xboole_0|r2_xboole_0(k1_xboole_0,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_xboole_1])])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))|~r2_xboole_0(k1_xboole_0,esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_46]), c_0_46]), c_0_25])).
% 0.20/0.38  cnf(c_0_49, plain, (X1=k1_xboole_0|r2_xboole_0(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_35, c_0_46])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_25])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_52]), c_0_25]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 54
% 0.20/0.38  # Proof object clause steps            : 33
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 23
% 0.20/0.38  # Proof object clause conjectures      : 20
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 14
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 14
% 0.20/0.38  # Proof object simplifying inferences  : 16
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 27
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 27
% 0.20/0.38  # Processed clauses                    : 96
% 0.20/0.38  # ...of these trivial                  : 3
% 0.20/0.38  # ...subsumed                          : 4
% 0.20/0.38  # ...remaining for further processing  : 89
% 0.20/0.38  # Other redundant clauses eliminated   : 8
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 23
% 0.20/0.38  # Generated clauses                    : 92
% 0.20/0.38  # ...of the previous two non-trivial   : 101
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 84
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 8
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 32
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 22
% 0.20/0.38  # Current number of unprocessed clauses: 55
% 0.20/0.38  # ...number of literals in the above   : 163
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 49
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 154
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 130
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.38  # Unit Clause-clause subsumption calls : 37
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 3
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2719
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.031 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.036 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

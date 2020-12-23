%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:51 EST 2020

% Result     : Theorem 1.03s
% Output     : CNFRefutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   40 (  96 expanded)
%              Number of clauses        :   29 (  45 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 299 expanded)
%              Number of equality atoms :   29 (  84 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t2_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
         => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(c_0_5,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_6,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & v1_zfmisc_1(X1) )
       => ! [X2] :
            ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
           => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t2_tex_2])).

fof(c_0_9,plain,(
    ! [X18,X19] :
      ( v1_xboole_0(X18)
      | v1_xboole_0(X19)
      | ~ v1_zfmisc_1(X19)
      | ~ r1_tarski(X18,X19)
      | X18 = X19 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_10,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v1_zfmisc_1(esk2_0)
    & ~ v1_xboole_0(k3_xboole_0(esk2_0,esk3_0))
    & ~ r1_tarski(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | v1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_zfmisc_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)) = esk2_0
    | v1_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X3,k4_xboole_0(X3,X4))
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)
    | r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = esk2_0
    | r2_hidden(esk1_3(X1,X2,esk2_0),esk3_0)
    | r2_hidden(esk1_3(X1,X2,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_11])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | r2_hidden(esk1_3(X1,X2,esk2_0),esk3_0)
    | r2_hidden(esk1_3(X1,X2,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_34]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_38]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.03/1.20  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 1.03/1.20  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.03/1.20  #
% 1.03/1.20  # Preprocessing time       : 0.019 s
% 1.03/1.20  # Presaturation interreduction done
% 1.03/1.20  
% 1.03/1.20  # Proof found!
% 1.03/1.20  # SZS status Theorem
% 1.03/1.20  # SZS output start CNFRefutation
% 1.03/1.20  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.03/1.20  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.03/1.20  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.03/1.20  fof(t2_tex_2, conjecture, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 1.03/1.20  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.03/1.20  fof(c_0_5, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.03/1.20  fof(c_0_6, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.03/1.20  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.03/1.20  fof(c_0_8, negated_conjecture, ~(![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t2_tex_2])).
% 1.03/1.20  fof(c_0_9, plain, ![X18, X19]:(v1_xboole_0(X18)|(v1_xboole_0(X19)|~v1_zfmisc_1(X19)|(~r1_tarski(X18,X19)|X18=X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 1.03/1.20  cnf(c_0_10, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.03/1.20  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.03/1.20  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.03/1.20  fof(c_0_13, negated_conjecture, ((~v1_xboole_0(esk2_0)&v1_zfmisc_1(esk2_0))&(~v1_xboole_0(k3_xboole_0(esk2_0,esk3_0))&~r1_tarski(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 1.03/1.20  cnf(c_0_14, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.03/1.20  cnf(c_0_15, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 1.03/1.20  cnf(c_0_16, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_12, c_0_11])).
% 1.03/1.20  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.03/1.20  cnf(c_0_18, negated_conjecture, (~v1_xboole_0(k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.03/1.20  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|v1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.03/1.20  cnf(c_0_20, negated_conjecture, (v1_zfmisc_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.03/1.20  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.03/1.20  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_16])).
% 1.03/1.20  cnf(c_0_23, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_17, c_0_11])).
% 1.03/1.20  cnf(c_0_24, negated_conjecture, (~v1_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_18, c_0_11])).
% 1.03/1.20  cnf(c_0_25, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))=esk2_0|v1_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 1.03/1.20  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.03/1.20  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X3,k4_xboole_0(X3,X4))|r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)|r2_hidden(esk1_3(X3,X4,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.03/1.20  cnf(c_0_28, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.03/1.20  cnf(c_0_29, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.03/1.20  cnf(c_0_30, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_26, c_0_11])).
% 1.03/1.20  cnf(c_0_31, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=esk2_0|r2_hidden(esk1_3(X1,X2,esk2_0),esk3_0)|r2_hidden(esk1_3(X1,X2,esk2_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.03/1.20  cnf(c_0_32, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_29, c_0_11])).
% 1.03/1.20  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_30])).
% 1.03/1.20  cnf(c_0_34, negated_conjecture, (r1_tarski(esk2_0,X1)|r2_hidden(esk1_3(X1,X2,esk2_0),esk3_0)|r2_hidden(esk1_3(X1,X2,esk2_0),X1)), inference(spm,[status(thm)],[c_0_15, c_0_31])).
% 1.03/1.20  cnf(c_0_35, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.03/1.20  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_33])).
% 1.03/1.20  cnf(c_0_37, negated_conjecture, (r2_hidden(esk1_3(esk3_0,X1,esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_34]), c_0_35])).
% 1.03/1.20  cnf(c_0_38, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.03/1.20  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_38]), c_0_35]), ['proof']).
% 1.03/1.20  # SZS output end CNFRefutation
% 1.03/1.20  # Proof object total steps             : 40
% 1.03/1.20  # Proof object clause steps            : 29
% 1.03/1.20  # Proof object formula steps           : 11
% 1.03/1.20  # Proof object conjectures             : 15
% 1.03/1.20  # Proof object clause conjectures      : 12
% 1.03/1.20  # Proof object formula conjectures     : 3
% 1.03/1.20  # Proof object initial clauses used    : 11
% 1.03/1.20  # Proof object initial formulas used   : 5
% 1.03/1.20  # Proof object generating inferences   : 11
% 1.03/1.20  # Proof object simplifying inferences  : 11
% 1.03/1.20  # Training examples: 0 positive, 0 negative
% 1.03/1.20  # Parsed axioms                        : 5
% 1.03/1.20  # Removed by relevancy pruning/SinE    : 0
% 1.03/1.20  # Initial clauses                      : 13
% 1.03/1.20  # Removed in clause preprocessing      : 1
% 1.03/1.20  # Initial clauses in saturation        : 12
% 1.03/1.20  # Processed clauses                    : 1162
% 1.03/1.20  # ...of these trivial                  : 7
% 1.03/1.20  # ...subsumed                          : 584
% 1.03/1.20  # ...remaining for further processing  : 571
% 1.03/1.20  # Other redundant clauses eliminated   : 3
% 1.03/1.20  # Clauses deleted for lack of memory   : 0
% 1.03/1.20  # Backward-subsumed                    : 69
% 1.03/1.20  # Backward-rewritten                   : 49
% 1.03/1.20  # Generated clauses                    : 55306
% 1.03/1.20  # ...of the previous two non-trivial   : 52961
% 1.03/1.20  # Contextual simplify-reflections      : 52
% 1.03/1.20  # Paramodulations                      : 54867
% 1.03/1.20  # Factorizations                       : 436
% 1.03/1.20  # Equation resolutions                 : 3
% 1.03/1.20  # Propositional unsat checks           : 0
% 1.03/1.20  #    Propositional check models        : 0
% 1.03/1.20  #    Propositional check unsatisfiable : 0
% 1.03/1.20  #    Propositional clauses             : 0
% 1.03/1.20  #    Propositional clauses after purity: 0
% 1.03/1.20  #    Propositional unsat core size     : 0
% 1.03/1.20  #    Propositional preprocessing time  : 0.000
% 1.03/1.20  #    Propositional encoding time       : 0.000
% 1.03/1.20  #    Propositional solver time         : 0.000
% 1.03/1.20  #    Success case prop preproc time    : 0.000
% 1.03/1.20  #    Success case prop encoding time   : 0.000
% 1.03/1.20  #    Success case prop solver time     : 0.000
% 1.03/1.20  # Current number of processed clauses  : 438
% 1.03/1.20  #    Positive orientable unit clauses  : 12
% 1.03/1.20  #    Positive unorientable unit clauses: 0
% 1.03/1.20  #    Negative unit clauses             : 2
% 1.03/1.20  #    Non-unit-clauses                  : 424
% 1.03/1.20  # Current number of unprocessed clauses: 51411
% 1.03/1.20  # ...number of literals in the above   : 327083
% 1.03/1.20  # Current number of archived formulas  : 0
% 1.03/1.20  # Current number of archived clauses   : 131
% 1.03/1.20  # Clause-clause subsumption calls (NU) : 40630
% 1.03/1.20  # Rec. Clause-clause subsumption calls : 12720
% 1.03/1.20  # Non-unit clause-clause subsumptions  : 684
% 1.03/1.20  # Unit Clause-clause subsumption calls : 976
% 1.03/1.20  # Rewrite failures with RHS unbound    : 0
% 1.03/1.20  # BW rewrite match attempts            : 40
% 1.03/1.20  # BW rewrite match successes           : 16
% 1.03/1.20  # Condensation attempts                : 0
% 1.03/1.20  # Condensation successes               : 0
% 1.03/1.20  # Termbank termtop insertions          : 1431562
% 1.03/1.20  
% 1.03/1.20  # -------------------------------------------------
% 1.03/1.20  # User time                : 0.825 s
% 1.03/1.20  # System time              : 0.028 s
% 1.03/1.20  # Total time               : 0.853 s
% 1.03/1.20  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

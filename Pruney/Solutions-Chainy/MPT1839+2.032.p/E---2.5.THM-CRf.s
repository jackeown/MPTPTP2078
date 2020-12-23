%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:50 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 486 expanded)
%              Number of clauses        :   36 ( 210 expanded)
%              Number of leaves         :   13 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 928 expanded)
%              Number of equality atoms :   45 ( 328 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
         => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t1_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & v1_zfmisc_1(X1) )
       => ! [X2] :
            ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
           => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t2_tex_2])).

fof(c_0_14,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | v1_xboole_0(X30)
      | ~ v1_zfmisc_1(X30)
      | ~ r1_tarski(X29,X30)
      | X29 = X30 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & v1_zfmisc_1(esk3_0)
    & ~ v1_xboole_0(k3_xboole_0(esk3_0,esk4_0))
    & ~ r1_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_18,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_zfmisc_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( X1 = esk3_0
    | v1_xboole_0(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_27]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1)) = esk3_0
    | v1_xboole_0(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_40,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_41,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k4_xboole_0(X18,X19) = X18 )
      & ( k4_xboole_0(X18,X19) != X18
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_42,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = esk3_0
    | v1_xboole_0(k5_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_43])).

fof(c_0_48,plain,(
    ! [X27] :
      ( ( r2_hidden(esk2_1(X27),X27)
        | X27 = k1_xboole_0 )
      & ( r1_xboole_0(esk2_1(X27),X27)
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_35]),c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_51,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) != X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_35]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = esk3_0
    | ~ r2_hidden(X1,k5_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_39]),c_0_50])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    | k5_xboole_0(esk3_0,esk3_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_27]),c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_55,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_39]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.20/0.40  # and selection function SelectCQIArNpEqFirst.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.047 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t2_tex_2, conjecture, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 0.20/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 0.20/0.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.40  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.40  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.40  fof(t1_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.20/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.40  fof(c_0_13, negated_conjecture, ~(![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t2_tex_2])).
% 0.20/0.40  fof(c_0_14, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.40  fof(c_0_15, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_16, plain, ![X29, X30]:(v1_xboole_0(X29)|(v1_xboole_0(X30)|~v1_zfmisc_1(X30)|(~r1_tarski(X29,X30)|X29=X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.20/0.40  fof(c_0_17, negated_conjecture, ((~v1_xboole_0(esk3_0)&v1_zfmisc_1(esk3_0))&(~v1_xboole_0(k3_xboole_0(esk3_0,esk4_0))&~r1_tarski(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.20/0.40  fof(c_0_18, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.40  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  fof(c_0_21, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_22, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.40  cnf(c_0_23, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (v1_zfmisc_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_26, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.40  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  fof(c_0_29, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.40  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (X1=esk3_0|v1_xboole_0(X1)|~r1_tarski(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.20/0.40  cnf(c_0_33, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.20/0.40  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_30, c_0_27])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (~v1_xboole_0(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_27]), c_0_28])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1))=esk3_0|v1_xboole_0(k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,X1)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.40  cnf(c_0_38, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_28])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.40  fof(c_0_40, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.40  fof(c_0_41, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k4_xboole_0(X18,X19)=X18)&(k4_xboole_0(X18,X19)!=X18|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.40  fof(c_0_42, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_44, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_46, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=esk3_0|v1_xboole_0(k5_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_43])).
% 0.20/0.40  fof(c_0_48, plain, ![X27]:((r2_hidden(esk2_1(X27),X27)|X27=k1_xboole_0)&(r1_xboole_0(esk2_1(X27),X27)|X27=k1_xboole_0)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).
% 0.20/0.40  cnf(c_0_49, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_35]), c_0_28])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_51, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.40  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))!=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_35]), c_0_28])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=esk3_0|~r2_hidden(X1,k5_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.40  cnf(c_0_54, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_39]), c_0_50])).
% 0.20/0.40  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)|k5_xboole_0(esk3_0,esk3_0)!=esk3_0), inference(spm,[status(thm)],[c_0_52, c_0_39])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.20/0.40  cnf(c_0_59, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_27]), c_0_28])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_55, c_0_58])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_39]), c_0_61]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 63
% 0.20/0.40  # Proof object clause steps            : 36
% 0.20/0.40  # Proof object formula steps           : 27
% 0.20/0.40  # Proof object conjectures             : 20
% 0.20/0.40  # Proof object clause conjectures      : 17
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 16
% 0.20/0.40  # Proof object initial formulas used   : 13
% 0.20/0.40  # Proof object generating inferences   : 10
% 0.20/0.40  # Proof object simplifying inferences  : 22
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 13
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 21
% 0.20/0.40  # Removed in clause preprocessing      : 4
% 0.20/0.40  # Initial clauses in saturation        : 17
% 0.20/0.40  # Processed clauses                    : 47
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 1
% 0.20/0.40  # ...remaining for further processing  : 46
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 7
% 0.20/0.40  # Generated clauses                    : 20
% 0.20/0.40  # ...of the previous two non-trivial   : 22
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 20
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 22
% 0.20/0.40  #    Positive orientable unit clauses  : 7
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 12
% 0.20/0.40  # Current number of unprocessed clauses: 9
% 0.20/0.40  # ...number of literals in the above   : 14
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 28
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 16
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 6
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.40  # Unit Clause-clause subsumption calls : 11
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 4
% 0.20/0.40  # BW rewrite match successes           : 3
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 1446
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.051 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.054 s
% 0.20/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:51:37 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 277 expanded)
%              Number of clauses        :   37 ( 131 expanded)
%              Number of leaves         :    7 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  156 ( 863 expanded)
%              Number of equality atoms :   22 ( 131 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_7,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(k1_tarski(X14),X15)
      | ~ r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_8,plain,(
    ! [X13] : r1_xboole_0(X13,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_9,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X18),X16)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X16)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(esk3_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(X25,esk3_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk4_2(X22,X23),esk3_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X27,X28,X29,X31] :
      ( ( r2_hidden(esk5_3(X27,X28,X29),k2_relat_1(X29))
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(X27,esk5_3(X27,X28,X29)),X29)
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk5_3(X27,X28,X29),X28)
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(X31,k2_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X31),X29)
        | ~ r2_hidden(X31,X28)
        | r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_15,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_16,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk5_3(esk1_2(X1,k10_relat_1(X2,X3)),X3,X2),X3)
    | r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk5_3(esk1_2(X1,k10_relat_1(X2,X3)),X3,X2),X4)
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_3(esk1_2(X1,k10_relat_1(X2,X3)),X3,X2),k2_relat_1(X2))
    | r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k10_relat_1(esk7_0,esk6_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk7_0),esk6_0) )
    & ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | r1_xboole_0(X4,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk1_2(X4,k2_relat_1(X2))),X2)
    | ~ r2_hidden(esk1_2(X4,k2_relat_1(X2)),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk3_2(k1_xboole_0,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_36,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk3_2(X2,X1),k2_relat_1(X2))
    | r2_hidden(esk3_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_13])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k2_relat_1(X2),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | r1_xboole_0(X3,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk1_2(X3,k2_relat_1(X2))),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,k2_relat_1(X1),esk1_2(X2,k2_relat_1(X1))),esk1_2(X2,k2_relat_1(X1))),X1)
    | r1_xboole_0(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_19]),c_0_19])]),c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | r1_xboole_0(X1,k10_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_44,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),esk1_2(X2,k2_relat_1(X1))),k10_relat_1(X1,X2))
    | r1_xboole_0(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk7_0,esk6_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk6_0,k2_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_39])]),c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.80/4.03  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 3.80/4.03  # and selection function SelectNewComplexAHP.
% 3.80/4.03  #
% 3.80/4.03  # Preprocessing time       : 0.027 s
% 3.80/4.03  
% 3.80/4.03  # Proof found!
% 3.80/4.03  # SZS status Theorem
% 3.80/4.03  # SZS output start CNFRefutation
% 3.80/4.03  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.80/4.03  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.80/4.03  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.80/4.03  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 3.80/4.03  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.80/4.03  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 3.80/4.03  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.80/4.03  fof(c_0_7, plain, ![X14, X15]:(~r1_xboole_0(k1_tarski(X14),X15)|~r2_hidden(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 3.80/4.03  fof(c_0_8, plain, ![X13]:r1_xboole_0(X13,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 3.80/4.03  cnf(c_0_9, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 3.80/4.03  cnf(c_0_10, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.80/4.03  fof(c_0_11, plain, ![X16, X17, X18, X20, X21, X22, X23, X25]:(((~r2_hidden(X18,X17)|r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X18),X16)|X17!=k2_relat_1(X16))&(~r2_hidden(k4_tarski(X21,X20),X16)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)))&((~r2_hidden(esk3_2(X22,X23),X23)|~r2_hidden(k4_tarski(X25,esk3_2(X22,X23)),X22)|X23=k2_relat_1(X22))&(r2_hidden(esk3_2(X22,X23),X23)|r2_hidden(k4_tarski(esk4_2(X22,X23),esk3_2(X22,X23)),X22)|X23=k2_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 3.80/4.03  cnf(c_0_12, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 3.80/4.03  cnf(c_0_13, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.80/4.03  fof(c_0_14, plain, ![X27, X28, X29, X31]:((((r2_hidden(esk5_3(X27,X28,X29),k2_relat_1(X29))|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29))&(r2_hidden(k4_tarski(X27,esk5_3(X27,X28,X29)),X29)|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29)))&(r2_hidden(esk5_3(X27,X28,X29),X28)|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29)))&(~r2_hidden(X31,k2_relat_1(X29))|~r2_hidden(k4_tarski(X27,X31),X29)|~r2_hidden(X31,X28)|r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 3.80/4.03  fof(c_0_15, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 3.80/4.03  cnf(c_0_16, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 3.80/4.03  cnf(c_0_17, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.80/4.03  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.80/4.03  cnf(c_0_19, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_16])).
% 3.80/4.03  cnf(c_0_20, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.80/4.03  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.80/4.03  cnf(c_0_22, plain, (r2_hidden(esk5_3(esk1_2(X1,k10_relat_1(X2,X3)),X3,X2),X3)|r1_xboole_0(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 3.80/4.03  cnf(c_0_23, plain, (r2_hidden(esk5_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.80/4.03  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 3.80/4.03  cnf(c_0_25, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.80/4.03  cnf(c_0_26, plain, (r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.80/4.03  cnf(c_0_27, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_16, c_0_19])).
% 3.80/4.03  cnf(c_0_28, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_20])).
% 3.80/4.03  cnf(c_0_29, plain, (r1_xboole_0(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(esk5_3(esk1_2(X1,k10_relat_1(X2,X3)),X3,X2),X4)|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 3.80/4.03  cnf(c_0_30, plain, (r2_hidden(esk5_3(esk1_2(X1,k10_relat_1(X2,X3)),X3,X2),k2_relat_1(X2))|r1_xboole_0(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 3.80/4.03  fof(c_0_31, negated_conjecture, (v1_relat_1(esk7_0)&((k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk7_0),esk6_0))&(k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 3.80/4.03  cnf(c_0_32, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|r1_xboole_0(X4,k2_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,esk1_2(X4,k2_relat_1(X2))),X2)|~r2_hidden(esk1_2(X4,k2_relat_1(X2)),X3)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 3.80/4.03  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.80/4.03  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk2_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_26])).
% 3.80/4.03  cnf(c_0_35, plain, (X1=k1_xboole_0|~r2_hidden(esk3_2(k1_xboole_0,X1),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 3.80/4.03  cnf(c_0_36, plain, (X1=k2_relat_1(X2)|r2_hidden(esk3_2(X2,X1),k2_relat_1(X2))|r2_hidden(esk3_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_28, c_0_13])).
% 3.80/4.03  cnf(c_0_37, plain, (r1_xboole_0(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r1_xboole_0(k2_relat_1(X2),X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 3.80/4.03  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.80/4.03  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.80/4.03  cnf(c_0_40, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|r1_xboole_0(X3,k2_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,esk1_2(X3,k2_relat_1(X2))),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 3.80/4.03  cnf(c_0_41, plain, (r2_hidden(k4_tarski(esk2_3(X1,k2_relat_1(X1),esk1_2(X2,k2_relat_1(X1))),esk1_2(X2,k2_relat_1(X1))),X1)|r1_xboole_0(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_18])).
% 3.80/4.03  cnf(c_0_42, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_19]), c_0_19])]), c_0_12])).
% 3.80/4.03  cnf(c_0_43, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(X1,k10_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 3.80/4.03  fof(c_0_44, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 3.80/4.03  cnf(c_0_45, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),esk1_2(X2,k2_relat_1(X1))),k10_relat_1(X1,X2))|r1_xboole_0(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.80/4.03  cnf(c_0_46, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 3.80/4.03  cnf(c_0_47, negated_conjecture, (k10_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.80/4.03  cnf(c_0_48, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.80/4.03  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk6_0,k2_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_39])]), c_0_12])).
% 3.80/4.03  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_46])])).
% 3.80/4.03  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), ['proof']).
% 3.80/4.03  # SZS output end CNFRefutation
% 3.80/4.03  # Proof object total steps             : 52
% 3.80/4.03  # Proof object clause steps            : 37
% 3.80/4.03  # Proof object formula steps           : 15
% 3.80/4.03  # Proof object conjectures             : 11
% 3.80/4.03  # Proof object clause conjectures      : 8
% 3.80/4.03  # Proof object formula conjectures     : 3
% 3.80/4.03  # Proof object initial clauses used    : 15
% 3.80/4.03  # Proof object initial formulas used   : 7
% 3.80/4.03  # Proof object generating inferences   : 20
% 3.80/4.03  # Proof object simplifying inferences  : 13
% 3.80/4.03  # Training examples: 0 positive, 0 negative
% 3.80/4.03  # Parsed axioms                        : 7
% 3.80/4.03  # Removed by relevancy pruning/SinE    : 0
% 3.80/4.03  # Initial clauses                      : 17
% 3.80/4.03  # Removed in clause preprocessing      : 0
% 3.80/4.03  # Initial clauses in saturation        : 17
% 3.80/4.03  # Processed clauses                    : 16210
% 3.80/4.03  # ...of these trivial                  : 0
% 3.80/4.03  # ...subsumed                          : 14772
% 3.80/4.03  # ...remaining for further processing  : 1438
% 3.80/4.03  # Other redundant clauses eliminated   : 142
% 3.80/4.03  # Clauses deleted for lack of memory   : 0
% 3.80/4.03  # Backward-subsumed                    : 413
% 3.80/4.03  # Backward-rewritten                   : 5
% 3.80/4.03  # Generated clauses                    : 192165
% 3.80/4.03  # ...of the previous two non-trivial   : 185198
% 3.80/4.03  # Contextual simplify-reflections      : 34
% 3.80/4.03  # Paramodulations                      : 191927
% 3.80/4.03  # Factorizations                       : 10
% 3.80/4.03  # Equation resolutions                 : 228
% 3.80/4.03  # Propositional unsat checks           : 0
% 3.80/4.03  #    Propositional check models        : 0
% 3.80/4.03  #    Propositional check unsatisfiable : 0
% 3.80/4.03  #    Propositional clauses             : 0
% 3.80/4.03  #    Propositional clauses after purity: 0
% 3.80/4.03  #    Propositional unsat core size     : 0
% 3.80/4.03  #    Propositional preprocessing time  : 0.000
% 3.80/4.03  #    Propositional encoding time       : 0.000
% 3.80/4.03  #    Propositional solver time         : 0.000
% 3.80/4.03  #    Success case prop preproc time    : 0.000
% 3.80/4.03  #    Success case prop encoding time   : 0.000
% 3.80/4.03  #    Success case prop solver time     : 0.000
% 3.80/4.03  # Current number of processed clauses  : 1020
% 3.80/4.03  #    Positive orientable unit clauses  : 7
% 3.80/4.03  #    Positive unorientable unit clauses: 0
% 3.80/4.03  #    Negative unit clauses             : 2
% 3.80/4.03  #    Non-unit-clauses                  : 1011
% 3.80/4.03  # Current number of unprocessed clauses: 167300
% 3.80/4.03  # ...number of literals in the above   : 1496280
% 3.80/4.03  # Current number of archived formulas  : 0
% 3.80/4.03  # Current number of archived clauses   : 418
% 3.80/4.03  # Clause-clause subsumption calls (NU) : 664279
% 3.80/4.03  # Rec. Clause-clause subsumption calls : 81255
% 3.80/4.03  # Non-unit clause-clause subsumptions  : 12797
% 3.80/4.03  # Unit Clause-clause subsumption calls : 23
% 3.80/4.03  # Rewrite failures with RHS unbound    : 0
% 3.80/4.03  # BW rewrite match attempts            : 2
% 3.80/4.03  # BW rewrite match successes           : 2
% 3.80/4.03  # Condensation attempts                : 0
% 3.80/4.03  # Condensation successes               : 0
% 3.80/4.03  # Termbank termtop insertions          : 6029807
% 3.80/4.04  
% 3.80/4.04  # -------------------------------------------------
% 3.80/4.04  # User time                : 3.562 s
% 3.80/4.04  # System time              : 0.093 s
% 3.80/4.04  # Total time               : 3.655 s
% 3.80/4.04  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

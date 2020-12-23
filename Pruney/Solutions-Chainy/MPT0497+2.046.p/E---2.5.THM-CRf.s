%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:39 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 146 expanded)
%              Number of clauses        :   32 (  63 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 504 expanded)
%              Number of equality atoms :   29 (  92 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_10,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,X21)
        | ~ r2_hidden(X20,k1_relat_1(k7_relat_1(X22,X21)))
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(X20,k1_relat_1(X22))
        | ~ r2_hidden(X20,k1_relat_1(k7_relat_1(X22,X21)))
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(X20,X21)
        | ~ r2_hidden(X20,k1_relat_1(X22))
        | r2_hidden(X20,k1_relat_1(k7_relat_1(X22,X21)))
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_12,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),k1_relat_1(X2))
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( k7_relat_1(esk4_0,esk3_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) )
    & ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk2_1(X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_24,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_1(k1_relat_1(k7_relat_1(X1,X2))),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k1_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X19] :
      ( ( k1_relat_1(X19) != k1_xboole_0
        | X19 = k1_xboole_0
        | ~ v1_relat_1(X19) )
      & ( k2_relat_1(X19) != k1_xboole_0
        | X19 = k1_xboole_0
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_29,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(k7_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,esk3_0)) = k1_xboole_0
    | k7_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_27])])).

fof(c_0_34,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k7_relat_1(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_35,plain,(
    ! [X15,X16] :
      ( ~ r1_xboole_0(k1_tarski(X15),X16)
      | ~ r2_hidden(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_36,plain,(
    ! [X14] : r1_xboole_0(X14,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X3)))
    | r1_xboole_0(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(X2)),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X1)))
    | r1_xboole_0(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_27])])).

cnf(c_0_45,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk3_0,k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_27])]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_44])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.14/0.38  # and selection function SelectNewComplexAHP.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.14/0.38  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 0.14/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.38  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 0.14/0.38  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.14/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.14/0.38  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.14/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.14/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.38  fof(c_0_10, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X20, X21, X22]:(((r2_hidden(X20,X21)|~r2_hidden(X20,k1_relat_1(k7_relat_1(X22,X21)))|~v1_relat_1(X22))&(r2_hidden(X20,k1_relat_1(X22))|~r2_hidden(X20,k1_relat_1(k7_relat_1(X22,X21)))|~v1_relat_1(X22)))&(~r2_hidden(X20,X21)|~r2_hidden(X20,k1_relat_1(X22))|r2_hidden(X20,k1_relat_1(k7_relat_1(X22,X21)))|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.38  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 0.14/0.38  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),k1_relat_1(X2))|r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  fof(c_0_22, negated_conjecture, (v1_relat_1(esk4_0)&((k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0))&(k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.14/0.38  cnf(c_0_23, plain, (X1=k1_xboole_0|~r2_hidden(esk2_1(X1),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 0.14/0.38  cnf(c_0_24, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_xboole_0|r2_hidden(esk2_1(k1_relat_1(k7_relat_1(X1,X2))),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.14/0.38  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)|~r1_xboole_0(k1_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  fof(c_0_28, plain, ![X19]:((k1_relat_1(X19)!=k1_xboole_0|X19=k1_xboole_0|~v1_relat_1(X19))&(k2_relat_1(X19)!=k1_xboole_0|X19=k1_xboole_0|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.14/0.38  cnf(c_0_29, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(k7_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.14/0.38  cnf(c_0_31, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,esk3_0))=k1_xboole_0|k7_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_27])])).
% 0.14/0.38  fof(c_0_34, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k7_relat_1(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.14/0.38  fof(c_0_35, plain, ![X15, X16]:(~r1_xboole_0(k1_tarski(X15),X16)|~r2_hidden(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.14/0.38  fof(c_0_36, plain, ![X14]:r1_xboole_0(X14,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.38  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X3)))|r1_xboole_0(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(esk1_2(X1,k1_relat_1(X2)),X3)), inference(spm,[status(thm)],[c_0_31, c_0_16])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0|~v1_relat_1(k7_relat_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.38  cnf(c_0_39, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_40, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.38  cnf(c_0_41, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.38  fof(c_0_42, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.14/0.38  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X1)))|r1_xboole_0(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_37, c_0_14])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_27])])).
% 0.14/0.38  cnf(c_0_45, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.38  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_48, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk3_0,k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_27])]), c_0_46])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_44])])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 52
% 0.14/0.38  # Proof object clause steps            : 32
% 0.14/0.38  # Proof object formula steps           : 20
% 0.14/0.38  # Proof object conjectures             : 13
% 0.14/0.38  # Proof object clause conjectures      : 10
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 16
% 0.14/0.38  # Proof object initial formulas used   : 10
% 0.14/0.38  # Proof object generating inferences   : 15
% 0.14/0.38  # Proof object simplifying inferences  : 13
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 10
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 18
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 18
% 0.14/0.38  # Processed clauses                    : 158
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 81
% 0.14/0.38  # ...remaining for further processing  : 76
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 13
% 0.14/0.38  # Generated clauses                    : 436
% 0.14/0.38  # ...of the previous two non-trivial   : 304
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 436
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 62
% 0.14/0.38  #    Positive orientable unit clauses  : 9
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 51
% 0.14/0.38  # Current number of unprocessed clauses: 118
% 0.14/0.38  # ...number of literals in the above   : 435
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 14
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 480
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 426
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 61
% 0.14/0.38  # Unit Clause-clause subsumption calls : 11
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 3
% 0.14/0.38  # BW rewrite match successes           : 3
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 7946
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.034 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.040 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

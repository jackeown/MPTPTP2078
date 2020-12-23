%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:12 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 198 expanded)
%              Number of clauses        :   34 (  86 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  179 ( 605 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t30_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v1_ordinal1(X19)
        | ~ r2_hidden(X20,X19)
        | r1_tarski(X20,X19) )
      & ( r2_hidden(esk3_1(X21),X21)
        | v1_ordinal1(X21) )
      & ( ~ r1_tarski(esk3_1(X21),X21)
        | v1_ordinal1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(k3_tarski(X14),X15) )
      & ( ~ r1_tarski(esk2_2(X14,X15),X15)
        | r1_tarski(k3_tarski(X14),X15) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_16,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | r1_tarski(X12,k3_tarski(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( ~ v1_ordinal1(X25)
      | ~ v3_ordinal1(X26)
      | ~ r2_xboole_0(X25,X26)
      | r2_hidden(X25,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | ~ r2_xboole_0(X10,X11) )
      & ( X10 != X11
        | ~ r2_xboole_0(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | X10 = X11
        | r2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_tarski(X1),X1)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v3_ordinal1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t30_ordinal1])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X2)
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ r2_hidden(esk3_1(k3_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_31,plain,(
    ! [X17,X18] :
      ( ~ v3_ordinal1(X17)
      | ~ v3_ordinal1(X18)
      | r1_ordinal1(X17,X18)
      | r1_ordinal1(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_32,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & ~ v3_ordinal1(k3_tarski(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_33,plain,(
    ! [X27,X28] :
      ( ~ v3_ordinal1(X28)
      | ~ r2_hidden(X27,X28)
      | v3_ordinal1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_34,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_36,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k3_tarski(X1) = X2
    | r2_hidden(k3_tarski(X1),X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_40,plain,(
    ! [X23,X24] :
      ( ( ~ r1_ordinal1(X23,X24)
        | r1_tarski(X23,X24)
        | ~ v3_ordinal1(X23)
        | ~ v3_ordinal1(X24) )
      & ( ~ r1_tarski(X23,X24)
        | r1_ordinal1(X23,X24)
        | ~ v3_ordinal1(X23)
        | ~ v3_ordinal1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_ordinal1(esk4_0,X1)
    | r1_ordinal1(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( v1_ordinal1(X1)
    | v3_ordinal1(esk3_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_43,plain,
    ( k3_tarski(X1) = X2
    | v3_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( v1_ordinal1(X1)
    | r1_ordinal1(esk3_1(X1),esk4_0)
    | r1_ordinal1(esk4_0,esk3_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k3_tarski(X1) = X1
    | v3_ordinal1(k3_tarski(X1))
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

fof(c_0_48,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_49,negated_conjecture,
    ( v1_ordinal1(X1)
    | r1_ordinal1(esk4_0,esk3_1(X1))
    | r1_tarski(esk3_1(X1),esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37])]),c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k3_tarski(esk4_0) = esk4_0
    | ~ v1_ordinal1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_37])])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( v1_ordinal1(X1)
    | r1_tarski(esk3_1(X1),esk4_0)
    | r1_tarski(esk4_0,esk3_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_49]),c_0_37])]),c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_ordinal1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_50]),c_0_37])])).

cnf(c_0_54,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(X1,esk3_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_52]),c_0_37])]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:44:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.21/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.042 s
% 0.21/0.47  
% 0.21/0.47  # Proof found!
% 0.21/0.47  # SZS status Theorem
% 0.21/0.47  # SZS output start CNFRefutation
% 0.21/0.47  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.21/0.47  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.21/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.47  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.21/0.47  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.21/0.47  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.21/0.47  fof(t30_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_ordinal1)).
% 0.21/0.47  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.21/0.47  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.21/0.47  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.21/0.47  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.47  fof(c_0_11, plain, ![X19, X20, X21]:((~v1_ordinal1(X19)|(~r2_hidden(X20,X19)|r1_tarski(X20,X19)))&((r2_hidden(esk3_1(X21),X21)|v1_ordinal1(X21))&(~r1_tarski(esk3_1(X21),X21)|v1_ordinal1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.21/0.47  fof(c_0_12, plain, ![X14, X15]:((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(k3_tarski(X14),X15))&(~r1_tarski(esk2_2(X14,X15),X15)|r1_tarski(k3_tarski(X14),X15))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.21/0.47  cnf(c_0_13, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.47  cnf(c_0_14, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.47  fof(c_0_15, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.47  cnf(c_0_16, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.47  cnf(c_0_17, plain, (r1_tarski(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.47  fof(c_0_18, plain, ![X12, X13]:(~r2_hidden(X12,X13)|r1_tarski(X12,k3_tarski(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.21/0.47  fof(c_0_19, plain, ![X25, X26]:(~v1_ordinal1(X25)|(~v3_ordinal1(X26)|(~r2_xboole_0(X25,X26)|r2_hidden(X25,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.21/0.47  fof(c_0_20, plain, ![X10, X11]:(((r1_tarski(X10,X11)|~r2_xboole_0(X10,X11))&(X10!=X11|~r2_xboole_0(X10,X11)))&(~r1_tarski(X10,X11)|X10=X11|r2_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.21/0.47  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.47  cnf(c_0_22, plain, (r1_tarski(k3_tarski(X1),X1)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.47  cnf(c_0_23, plain, (v1_ordinal1(X1)|~r1_tarski(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.47  cnf(c_0_24, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.47  fof(c_0_25, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t30_ordinal1])).
% 0.21/0.47  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.47  cnf(c_0_27, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.47  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X2)|~r2_hidden(X1,k3_tarski(X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.47  cnf(c_0_29, plain, (r2_hidden(esk3_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.47  cnf(c_0_30, plain, (v1_ordinal1(k3_tarski(X1))|~r2_hidden(esk3_1(k3_tarski(X1)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.47  fof(c_0_31, plain, ![X17, X18]:(~v3_ordinal1(X17)|~v3_ordinal1(X18)|(r1_ordinal1(X17,X18)|r1_ordinal1(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.21/0.47  fof(c_0_32, negated_conjecture, (v3_ordinal1(esk4_0)&~v3_ordinal1(k3_tarski(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.21/0.47  fof(c_0_33, plain, ![X27, X28]:(~v3_ordinal1(X28)|(~r2_hidden(X27,X28)|v3_ordinal1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.21/0.47  cnf(c_0_34, plain, (X1=X2|r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.47  cnf(c_0_35, plain, (v1_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.21/0.47  cnf(c_0_36, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.47  cnf(c_0_37, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.47  cnf(c_0_38, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.47  cnf(c_0_39, plain, (k3_tarski(X1)=X2|r2_hidden(k3_tarski(X1),X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.47  fof(c_0_40, plain, ![X23, X24]:((~r1_ordinal1(X23,X24)|r1_tarski(X23,X24)|(~v3_ordinal1(X23)|~v3_ordinal1(X24)))&(~r1_tarski(X23,X24)|r1_ordinal1(X23,X24)|(~v3_ordinal1(X23)|~v3_ordinal1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.21/0.47  cnf(c_0_41, negated_conjecture, (r1_ordinal1(esk4_0,X1)|r1_ordinal1(X1,esk4_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.47  cnf(c_0_42, plain, (v1_ordinal1(X1)|v3_ordinal1(esk3_1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 0.21/0.47  cnf(c_0_43, plain, (k3_tarski(X1)=X2|v3_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.47  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.47  cnf(c_0_45, negated_conjecture, (v1_ordinal1(X1)|r1_ordinal1(esk3_1(X1),esk4_0)|r1_ordinal1(esk4_0,esk3_1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.47  cnf(c_0_46, negated_conjecture, (~v3_ordinal1(k3_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.47  cnf(c_0_47, plain, (k3_tarski(X1)=X1|v3_ordinal1(k3_tarski(X1))|~v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_22])).
% 0.21/0.47  fof(c_0_48, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.47  cnf(c_0_49, negated_conjecture, (v1_ordinal1(X1)|r1_ordinal1(esk4_0,esk3_1(X1))|r1_tarski(esk3_1(X1),esk4_0)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37])]), c_0_42])).
% 0.21/0.47  cnf(c_0_50, negated_conjecture, (k3_tarski(esk4_0)=esk4_0|~v1_ordinal1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_37])])).
% 0.21/0.47  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.47  cnf(c_0_52, negated_conjecture, (v1_ordinal1(X1)|r1_tarski(esk3_1(X1),esk4_0)|r1_tarski(esk4_0,esk3_1(X1))|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_49]), c_0_37])]), c_0_42])).
% 0.21/0.47  cnf(c_0_53, negated_conjecture, (~v1_ordinal1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_50]), c_0_37])])).
% 0.21/0.47  cnf(c_0_54, plain, (v1_ordinal1(X1)|~r1_tarski(X1,esk3_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_29])).
% 0.21/0.47  cnf(c_0_55, negated_conjecture, (r1_tarski(esk4_0,esk3_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_52]), c_0_37])]), c_0_53])).
% 0.21/0.47  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_53]), ['proof']).
% 0.21/0.47  # SZS output end CNFRefutation
% 0.21/0.47  # Proof object total steps             : 57
% 0.21/0.47  # Proof object clause steps            : 34
% 0.21/0.47  # Proof object formula steps           : 23
% 0.21/0.47  # Proof object conjectures             : 13
% 0.21/0.47  # Proof object clause conjectures      : 10
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 15
% 0.21/0.47  # Proof object initial formulas used   : 11
% 0.21/0.47  # Proof object generating inferences   : 19
% 0.21/0.47  # Proof object simplifying inferences  : 15
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 11
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 20
% 0.21/0.47  # Removed in clause preprocessing      : 0
% 0.21/0.47  # Initial clauses in saturation        : 20
% 0.21/0.47  # Processed clauses                    : 381
% 0.21/0.47  # ...of these trivial                  : 0
% 0.21/0.47  # ...subsumed                          : 155
% 0.21/0.47  # ...remaining for further processing  : 226
% 0.21/0.47  # Other redundant clauses eliminated   : 1
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 6
% 0.21/0.47  # Backward-rewritten                   : 0
% 0.21/0.47  # Generated clauses                    : 1846
% 0.21/0.47  # ...of the previous two non-trivial   : 1810
% 0.21/0.47  # Contextual simplify-reflections      : 7
% 0.21/0.47  # Paramodulations                      : 1844
% 0.21/0.47  # Factorizations                       : 0
% 0.21/0.47  # Equation resolutions                 : 1
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 218
% 0.21/0.47  #    Positive orientable unit clauses  : 5
% 0.21/0.47  #    Positive unorientable unit clauses: 0
% 0.21/0.47  #    Negative unit clauses             : 3
% 0.21/0.47  #    Non-unit-clauses                  : 210
% 0.21/0.47  # Current number of unprocessed clauses: 1448
% 0.21/0.47  # ...number of literals in the above   : 8087
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 7
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 5754
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 2871
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 60
% 0.21/0.47  # Unit Clause-clause subsumption calls : 171
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 8
% 0.21/0.47  # BW rewrite match successes           : 0
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 41706
% 0.21/0.47  
% 0.21/0.47  # -------------------------------------------------
% 0.21/0.47  # User time                : 0.121 s
% 0.21/0.47  # System time              : 0.007 s
% 0.21/0.47  # Total time               : 0.128 s
% 0.21/0.47  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

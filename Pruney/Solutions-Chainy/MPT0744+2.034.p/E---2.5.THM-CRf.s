%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 567 expanded)
%              Number of clauses        :   42 ( 235 expanded)
%              Number of leaves         :   11 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  169 (1739 expanded)
%              Number of equality atoms :   13 ( 102 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(t22_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ! [X3] :
              ( v3_ordinal1(X3)
             => ( ( r1_tarski(X1,X2)
                  & r2_hidden(X2,X3) )
               => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

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

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ~ v3_ordinal1(X15)
      | ~ v3_ordinal1(X16)
      | r1_ordinal1(X15,X16)
      | r1_ordinal1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_13,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ( ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0))
      | ~ r1_ordinal1(esk2_0,esk3_0) )
    & ( r2_hidden(esk2_0,k1_ordinal1(esk3_0))
      | r1_ordinal1(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_14,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_ordinal1(X23)
      | ~ v3_ordinal1(X24)
      | ~ v3_ordinal1(X25)
      | ~ r1_tarski(X23,X24)
      | ~ r2_hidden(X24,X25)
      | r2_hidden(X23,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).

fof(c_0_17,plain,(
    ! [X26,X27] :
      ( ~ v3_ordinal1(X27)
      | ~ r2_hidden(X26,X27)
      | v3_ordinal1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ( ~ r1_ordinal1(X18,X19)
        | r1_tarski(X18,X19)
        | ~ v3_ordinal1(X18)
        | ~ v3_ordinal1(X19) )
      & ( ~ r1_tarski(X18,X19)
        | r1_ordinal1(X18,X19)
        | ~ v3_ordinal1(X18)
        | ~ v3_ordinal1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_19,negated_conjecture,
    ( r1_ordinal1(X1,esk3_0)
    | r1_ordinal1(esk3_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X14] :
      ( ( v1_ordinal1(X14)
        | ~ v3_ordinal1(X14) )
      & ( v2_ordinal1(X14)
        | ~ v3_ordinal1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_22,plain,(
    ! [X28] :
      ( ~ v3_ordinal1(X28)
      | v3_ordinal1(k1_ordinal1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_23,plain,(
    ! [X17] : k1_ordinal1(X17) = k2_xboole_0(X17,k1_tarski(X17)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk2_0)
    | r1_ordinal1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X20] : r2_hidden(X20,k1_ordinal1(X20)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_30,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r1_ordinal1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_15]),c_0_20])])).

cnf(c_0_34,negated_conjecture,
    ( v1_ordinal1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X21,X22] :
      ( ( ~ r2_hidden(X21,k1_ordinal1(X22))
        | r2_hidden(X21,X22)
        | X21 = X22 )
      & ( ~ r2_hidden(X21,X22)
        | r2_hidden(X21,k1_ordinal1(X22)) )
      & ( X21 != X22
        | r2_hidden(X21,k1_ordinal1(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0))
    | ~ r1_ordinal1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk2_0)
    | r2_hidden(esk2_0,X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_15])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_0,k1_ordinal1(esk3_0))
    | r1_ordinal1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_ordinal1(esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk2_0)
    | r2_hidden(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_46,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk3_0)
    | r2_hidden(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_31])).

fof(c_0_48,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_49,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( esk2_0 = esk3_0
    | r1_ordinal1(esk2_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_49]),c_0_20]),c_0_15])])).

cnf(c_0_53,negated_conjecture,
    ( v1_ordinal1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = esk3_0
    | r1_tarski(esk2_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_50]),c_0_15]),c_0_20])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_52]),c_0_53])])).

cnf(c_0_57,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = esk3_0
    | r1_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_40]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( esk2_0 = esk3_0
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_58])).

cnf(c_0_61,plain,
    ( r1_ordinal1(X1,X1)
    | ~ v3_ordinal1(X1) ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_59]),c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_62]),c_0_63]),c_0_62]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:41:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.42  # and selection function PSelectComplexPreferEQ.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.047 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.19/0.42  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.19/0.42  fof(t22_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r1_tarski(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 0.19/0.42  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.19/0.42  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.19/0.42  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.19/0.42  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.19/0.42  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.19/0.42  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.19/0.42  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.19/0.42  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.42  fof(c_0_11, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.19/0.42  fof(c_0_12, plain, ![X15, X16]:(~v3_ordinal1(X15)|~v3_ordinal1(X16)|(r1_ordinal1(X15,X16)|r1_ordinal1(X16,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.19/0.42  fof(c_0_13, negated_conjecture, (v3_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&((~r2_hidden(esk2_0,k1_ordinal1(esk3_0))|~r1_ordinal1(esk2_0,esk3_0))&(r2_hidden(esk2_0,k1_ordinal1(esk3_0))|r1_ordinal1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.42  cnf(c_0_14, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_15, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  fof(c_0_16, plain, ![X23, X24, X25]:(~v1_ordinal1(X23)|(~v3_ordinal1(X24)|(~v3_ordinal1(X25)|(~r1_tarski(X23,X24)|~r2_hidden(X24,X25)|r2_hidden(X23,X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_ordinal1])])])).
% 0.19/0.42  fof(c_0_17, plain, ![X26, X27]:(~v3_ordinal1(X27)|(~r2_hidden(X26,X27)|v3_ordinal1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.19/0.42  fof(c_0_18, plain, ![X18, X19]:((~r1_ordinal1(X18,X19)|r1_tarski(X18,X19)|(~v3_ordinal1(X18)|~v3_ordinal1(X19)))&(~r1_tarski(X18,X19)|r1_ordinal1(X18,X19)|(~v3_ordinal1(X18)|~v3_ordinal1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.19/0.42  cnf(c_0_19, negated_conjecture, (r1_ordinal1(X1,esk3_0)|r1_ordinal1(esk3_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.42  cnf(c_0_20, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  fof(c_0_21, plain, ![X14]:((v1_ordinal1(X14)|~v3_ordinal1(X14))&(v2_ordinal1(X14)|~v3_ordinal1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.19/0.42  fof(c_0_22, plain, ![X28]:(~v3_ordinal1(X28)|v3_ordinal1(k1_ordinal1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.19/0.42  fof(c_0_23, plain, ![X17]:k1_ordinal1(X17)=k2_xboole_0(X17,k1_tarski(X17)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.19/0.42  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~v3_ordinal1(X3)|~r1_tarski(X1,X2)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_25, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_27, negated_conjecture, (r1_ordinal1(esk3_0,esk2_0)|r1_ordinal1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.42  cnf(c_0_28, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  fof(c_0_29, plain, ![X20]:r2_hidden(X20,k1_ordinal1(X20)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.19/0.42  cnf(c_0_30, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_31, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r1_tarski(X1,X3)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,esk3_0)|r1_ordinal1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_15]), c_0_20])])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (v1_ordinal1(esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_20])).
% 0.19/0.42  cnf(c_0_35, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_36, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.42  fof(c_0_37, plain, ![X21, X22]:((~r2_hidden(X21,k1_ordinal1(X22))|(r2_hidden(X21,X22)|X21=X22))&((~r2_hidden(X21,X22)|r2_hidden(X21,k1_ordinal1(X22)))&(X21!=X22|r2_hidden(X21,k1_ordinal1(X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk2_0,k1_ordinal1(esk3_0))|~r1_ordinal1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (r1_ordinal1(esk3_0,esk2_0)|r2_hidden(esk2_0,X1)|~v3_ordinal1(X1)|~r2_hidden(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.42  cnf(c_0_40, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_35, c_0_31])).
% 0.19/0.42  cnf(c_0_41, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))), inference(spm,[status(thm)],[c_0_36, c_0_15])).
% 0.19/0.42  cnf(c_0_42, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_0,k1_ordinal1(esk3_0))|r1_ordinal1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (~r1_ordinal1(esk2_0,esk3_0)|~r2_hidden(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))), inference(rw,[status(thm)],[c_0_38, c_0_31])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (r1_ordinal1(esk3_0,esk2_0)|r2_hidden(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.19/0.42  cnf(c_0_46, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_42, c_0_31])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (r1_ordinal1(esk2_0,esk3_0)|r2_hidden(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))), inference(rw,[status(thm)],[c_0_43, c_0_31])).
% 0.19/0.42  fof(c_0_48, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (r1_ordinal1(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_27])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (esk2_0=esk3_0|r1_ordinal1(esk2_0,esk3_0)|r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.42  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_49]), c_0_20]), c_0_15])])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (v1_ordinal1(esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_15])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (esk2_0=esk3_0|r1_tarski(esk2_0,esk3_0)|r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_50]), c_0_15]), c_0_20])])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_0,X1)|~v3_ordinal1(X1)|~r2_hidden(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_52]), c_0_53])])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(spm,[status(thm)],[c_0_36, c_0_20])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (esk2_0=esk3_0|r1_tarski(esk2_0,esk3_0)), inference(sr,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_40]), c_0_57])])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (esk2_0=esk3_0|~r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_58])).
% 0.19/0.42  cnf(c_0_61, plain, (r1_ordinal1(X1,X1)|~v3_ordinal1(X1)), inference(ef,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_62, negated_conjecture, (esk2_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_59]), c_0_60])).
% 0.19/0.42  cnf(c_0_63, negated_conjecture, (r1_ordinal1(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_61, c_0_15])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_62]), c_0_63]), c_0_62]), c_0_40])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 65
% 0.19/0.42  # Proof object clause steps            : 42
% 0.19/0.42  # Proof object formula steps           : 23
% 0.19/0.42  # Proof object conjectures             : 30
% 0.19/0.42  # Proof object clause conjectures      : 27
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 14
% 0.19/0.42  # Proof object initial formulas used   : 11
% 0.19/0.42  # Proof object generating inferences   : 20
% 0.19/0.42  # Proof object simplifying inferences  : 31
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 12
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 24
% 0.19/0.42  # Removed in clause preprocessing      : 1
% 0.19/0.42  # Initial clauses in saturation        : 23
% 0.19/0.42  # Processed clauses                    : 232
% 0.19/0.42  # ...of these trivial                  : 0
% 0.19/0.42  # ...subsumed                          : 43
% 0.19/0.42  # ...remaining for further processing  : 189
% 0.19/0.42  # Other redundant clauses eliminated   : 4
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 4
% 0.19/0.42  # Backward-rewritten                   : 85
% 0.19/0.42  # Generated clauses                    : 510
% 0.19/0.42  # ...of the previous two non-trivial   : 407
% 0.19/0.42  # Contextual simplify-reflections      : 3
% 0.19/0.42  # Paramodulations                      : 475
% 0.19/0.42  # Factorizations                       : 26
% 0.19/0.42  # Equation resolutions                 : 4
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 70
% 0.19/0.42  #    Positive orientable unit clauses  : 28
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 3
% 0.19/0.42  #    Non-unit-clauses                  : 39
% 0.19/0.42  # Current number of unprocessed clauses: 193
% 0.19/0.42  # ...number of literals in the above   : 505
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 116
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 1042
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 764
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 48
% 0.19/0.42  # Unit Clause-clause subsumption calls : 157
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 68
% 0.19/0.42  # BW rewrite match successes           : 5
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 13704
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.070 s
% 0.19/0.42  # System time              : 0.009 s
% 0.19/0.42  # Total time               : 0.079 s
% 0.19/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

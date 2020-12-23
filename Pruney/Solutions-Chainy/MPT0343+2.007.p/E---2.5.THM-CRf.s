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
% DateTime   : Thu Dec  3 10:45:05 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 119 expanded)
%              Number of clauses        :   41 (  56 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  182 ( 530 expanded)
%              Number of equality atoms :   28 (  69 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
             => X2 = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_subset_1])).

fof(c_0_9,plain,(
    ! [X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X28,X27)
        | r1_tarski(X28,X26)
        | X27 != k1_zfmisc_1(X26) )
      & ( ~ r1_tarski(X29,X26)
        | r2_hidden(X29,X27)
        | X27 != k1_zfmisc_1(X26) )
      & ( ~ r2_hidden(esk4_2(X30,X31),X31)
        | ~ r1_tarski(esk4_2(X30,X31),X30)
        | X31 = k1_zfmisc_1(X30) )
      & ( r2_hidden(esk4_2(X30,X31),X31)
        | r1_tarski(esk4_2(X30,X31),X30)
        | X31 = k1_zfmisc_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_10,plain,(
    ! [X33,X34] :
      ( ( ~ m1_subset_1(X34,X33)
        | r2_hidden(X34,X33)
        | v1_xboole_0(X33) )
      & ( ~ r2_hidden(X34,X33)
        | m1_subset_1(X34,X33)
        | v1_xboole_0(X33) )
      & ( ~ m1_subset_1(X34,X33)
        | v1_xboole_0(X34)
        | ~ v1_xboole_0(X33) )
      & ( ~ v1_xboole_0(X34)
        | m1_subset_1(X34,X33)
        | ~ v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X39] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))
      & ( ~ r2_hidden(X39,esk6_0)
        | r2_hidden(X39,esk7_0)
        | ~ m1_subset_1(X39,esk5_0) )
      & ( ~ r2_hidden(X39,esk7_0)
        | r2_hidden(X39,esk6_0)
        | ~ m1_subset_1(X39,esk5_0) )
      & esk6_0 != esk7_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

fof(c_0_12,plain,(
    ! [X35] : ~ v1_xboole_0(k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

fof(c_0_20,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | r2_hidden(esk2_2(esk6_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_2(esk6_0,X1),esk5_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | r2_hidden(esk2_2(esk6_0,X1),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk7_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_31]),c_0_16])).

fof(c_0_35,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k3_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X21)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X21)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k3_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_37])).

cnf(c_0_43,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk3_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(X1,X2) = esk6_0
    | r2_hidden(esk3_3(X1,X2,esk6_0),esk7_0)
    | r2_hidden(esk3_3(X1,X2,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ m1_subset_1(esk2_2(X1,esk6_0),esk5_0)
    | ~ r2_hidden(esk2_2(X1,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_26])).

fof(c_0_48,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk3_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk7_0,X1) = esk6_0
    | r2_hidden(esk3_3(esk7_0,X1,esk6_0),esk7_0) ),
    inference(ef,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0)
    | ~ m1_subset_1(esk2_2(esk7_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_2(esk7_0,X1),esk5_0)
    | r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_47])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk7_0,esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( esk6_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.59/0.79  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.59/0.79  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.59/0.79  #
% 0.59/0.79  # Preprocessing time       : 0.029 s
% 0.59/0.79  # Presaturation interreduction done
% 0.59/0.79  
% 0.59/0.79  # Proof found!
% 0.59/0.79  # SZS status Theorem
% 0.59/0.79  # SZS output start CNFRefutation
% 0.59/0.79  fof(t8_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 0.59/0.79  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.59/0.79  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.59/0.79  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.59/0.79  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.59/0.79  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.59/0.79  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.59/0.79  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.59/0.79  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X2=X3)))), inference(assume_negation,[status(cth)],[t8_subset_1])).
% 0.59/0.79  fof(c_0_9, plain, ![X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X28,X27)|r1_tarski(X28,X26)|X27!=k1_zfmisc_1(X26))&(~r1_tarski(X29,X26)|r2_hidden(X29,X27)|X27!=k1_zfmisc_1(X26)))&((~r2_hidden(esk4_2(X30,X31),X31)|~r1_tarski(esk4_2(X30,X31),X30)|X31=k1_zfmisc_1(X30))&(r2_hidden(esk4_2(X30,X31),X31)|r1_tarski(esk4_2(X30,X31),X30)|X31=k1_zfmisc_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.59/0.79  fof(c_0_10, plain, ![X33, X34]:(((~m1_subset_1(X34,X33)|r2_hidden(X34,X33)|v1_xboole_0(X33))&(~r2_hidden(X34,X33)|m1_subset_1(X34,X33)|v1_xboole_0(X33)))&((~m1_subset_1(X34,X33)|v1_xboole_0(X34)|~v1_xboole_0(X33))&(~v1_xboole_0(X34)|m1_subset_1(X34,X33)|~v1_xboole_0(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.59/0.79  fof(c_0_11, negated_conjecture, ![X39]:(m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))&(((~r2_hidden(X39,esk6_0)|r2_hidden(X39,esk7_0)|~m1_subset_1(X39,esk5_0))&(~r2_hidden(X39,esk7_0)|r2_hidden(X39,esk6_0)|~m1_subset_1(X39,esk5_0)))&esk6_0!=esk7_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).
% 0.59/0.79  fof(c_0_12, plain, ![X35]:~v1_xboole_0(k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.59/0.79  cnf(c_0_13, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.59/0.79  cnf(c_0_14, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.59/0.79  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.79  cnf(c_0_16, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.59/0.79  fof(c_0_17, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.59/0.79  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_13])).
% 0.59/0.79  cnf(c_0_19, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.59/0.79  fof(c_0_20, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.59/0.79  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.59/0.79  cnf(c_0_22, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.59/0.79  cnf(c_0_23, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.59/0.79  cnf(c_0_24, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.59/0.79  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.59/0.79  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.59/0.79  cnf(c_0_27, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.59/0.79  cnf(c_0_28, negated_conjecture, (r1_tarski(esk6_0,X1)|r2_hidden(esk2_2(esk6_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.59/0.79  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.79  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_2(esk6_0,X1),esk5_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.59/0.79  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.79  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.59/0.79  cnf(c_0_33, negated_conjecture, (r1_tarski(esk6_0,X1)|r2_hidden(esk2_2(esk6_0,X1),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_30])).
% 0.59/0.79  cnf(c_0_34, negated_conjecture, (r2_hidden(esk7_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_31]), c_0_16])).
% 0.59/0.79  fof(c_0_35, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k3_xboole_0(X15,X16))&(r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k3_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|~r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k3_xboole_0(X15,X16)))&((~r2_hidden(esk3_3(X20,X21,X22),X22)|(~r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(esk3_3(X20,X21,X22),X21))|X22=k3_xboole_0(X20,X21))&((r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k3_xboole_0(X20,X21))&(r2_hidden(esk3_3(X20,X21,X22),X21)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k3_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.59/0.79  cnf(c_0_36, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.59/0.79  cnf(c_0_37, negated_conjecture, (r1_tarski(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_34])).
% 0.59/0.79  cnf(c_0_38, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.59/0.79  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_36])).
% 0.59/0.79  cnf(c_0_40, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.59/0.79  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.79  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_37])).
% 0.59/0.79  cnf(c_0_43, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk3_3(X1,X2,X3),X3)|~r2_hidden(esk3_3(X1,X2,X3),X1)|~r2_hidden(esk3_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.59/0.79  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk3_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_38])).
% 0.59/0.79  cnf(c_0_45, negated_conjecture, (k3_xboole_0(X1,X2)=esk6_0|r2_hidden(esk3_3(X1,X2,esk6_0),esk7_0)|r2_hidden(esk3_3(X1,X2,esk6_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.59/0.79  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,esk6_0)|~m1_subset_1(esk2_2(X1,esk6_0),esk5_0)|~r2_hidden(esk2_2(X1,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_32, c_0_41])).
% 0.59/0.79  cnf(c_0_47, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_26])).
% 0.59/0.79  fof(c_0_48, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.59/0.79  cnf(c_0_49, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk3_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_44])).
% 0.59/0.79  cnf(c_0_50, negated_conjecture, (k3_xboole_0(esk7_0,X1)=esk6_0|r2_hidden(esk3_3(esk7_0,X1,esk6_0),esk7_0)), inference(ef,[status(thm)],[c_0_45])).
% 0.59/0.79  cnf(c_0_51, negated_conjecture, (r1_tarski(esk7_0,esk6_0)|~m1_subset_1(esk2_2(esk7_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_26])).
% 0.59/0.79  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk2_2(esk7_0,X1),esk5_0)|r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_47])).
% 0.59/0.79  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.59/0.79  cnf(c_0_54, negated_conjecture, (k3_xboole_0(esk7_0,esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.59/0.79  cnf(c_0_55, negated_conjecture, (r1_tarski(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.59/0.79  cnf(c_0_56, negated_conjecture, (esk6_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.79  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), c_0_56]), ['proof']).
% 0.59/0.79  # SZS output end CNFRefutation
% 0.59/0.79  # Proof object total steps             : 58
% 0.59/0.79  # Proof object clause steps            : 41
% 0.59/0.79  # Proof object formula steps           : 17
% 0.59/0.79  # Proof object conjectures             : 28
% 0.59/0.79  # Proof object clause conjectures      : 25
% 0.59/0.79  # Proof object formula conjectures     : 3
% 0.59/0.79  # Proof object initial clauses used    : 17
% 0.59/0.79  # Proof object initial formulas used   : 8
% 0.59/0.79  # Proof object generating inferences   : 22
% 0.59/0.79  # Proof object simplifying inferences  : 9
% 0.59/0.79  # Training examples: 0 positive, 0 negative
% 0.59/0.79  # Parsed axioms                        : 8
% 0.59/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.79  # Initial clauses                      : 26
% 0.59/0.79  # Removed in clause preprocessing      : 0
% 0.59/0.79  # Initial clauses in saturation        : 26
% 0.59/0.79  # Processed clauses                    : 4671
% 0.59/0.79  # ...of these trivial                  : 40
% 0.59/0.79  # ...subsumed                          : 3597
% 0.59/0.79  # ...remaining for further processing  : 1034
% 0.59/0.79  # Other redundant clauses eliminated   : 5
% 0.59/0.79  # Clauses deleted for lack of memory   : 0
% 0.59/0.79  # Backward-subsumed                    : 27
% 0.59/0.79  # Backward-rewritten                   : 105
% 0.59/0.79  # Generated clauses                    : 33382
% 0.59/0.79  # ...of the previous two non-trivial   : 31807
% 0.59/0.79  # Contextual simplify-reflections      : 14
% 0.59/0.79  # Paramodulations                      : 33264
% 0.59/0.79  # Factorizations                       : 100
% 0.59/0.79  # Equation resolutions                 : 5
% 0.59/0.79  # Propositional unsat checks           : 0
% 0.59/0.79  #    Propositional check models        : 0
% 0.59/0.79  #    Propositional check unsatisfiable : 0
% 0.59/0.79  #    Propositional clauses             : 0
% 0.59/0.79  #    Propositional clauses after purity: 0
% 0.59/0.79  #    Propositional unsat core size     : 0
% 0.59/0.79  #    Propositional preprocessing time  : 0.000
% 0.59/0.79  #    Propositional encoding time       : 0.000
% 0.59/0.79  #    Propositional solver time         : 0.000
% 0.59/0.79  #    Success case prop preproc time    : 0.000
% 0.59/0.79  #    Success case prop encoding time   : 0.000
% 0.59/0.79  #    Success case prop solver time     : 0.000
% 0.59/0.79  # Current number of processed clauses  : 858
% 0.59/0.79  #    Positive orientable unit clauses  : 141
% 0.59/0.79  #    Positive unorientable unit clauses: 0
% 0.59/0.79  #    Negative unit clauses             : 13
% 0.59/0.79  #    Non-unit-clauses                  : 704
% 0.59/0.79  # Current number of unprocessed clauses: 27000
% 0.59/0.79  # ...number of literals in the above   : 97588
% 0.59/0.79  # Current number of archived formulas  : 0
% 0.59/0.79  # Current number of archived clauses   : 171
% 0.59/0.79  # Clause-clause subsumption calls (NU) : 57319
% 0.59/0.79  # Rec. Clause-clause subsumption calls : 35880
% 0.59/0.79  # Non-unit clause-clause subsumptions  : 1407
% 0.59/0.79  # Unit Clause-clause subsumption calls : 8437
% 0.59/0.79  # Rewrite failures with RHS unbound    : 0
% 0.59/0.79  # BW rewrite match attempts            : 172
% 0.59/0.79  # BW rewrite match successes           : 3
% 0.59/0.79  # Condensation attempts                : 0
% 0.59/0.79  # Condensation successes               : 0
% 0.59/0.79  # Termbank termtop insertions          : 553239
% 0.59/0.79  
% 0.59/0.79  # -------------------------------------------------
% 0.59/0.79  # User time                : 0.427 s
% 0.59/0.79  # System time              : 0.019 s
% 0.59/0.79  # Total time               : 0.446 s
% 0.59/0.79  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:26 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   51 (  97 expanded)
%              Number of clauses        :   34 (  46 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 254 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(t42_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | r1_tarski(k4_xboole_0(X22,X21),k4_xboole_0(X22,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    inference(assume_negation,[status(cth)],[t42_subset_1])).

fof(c_0_20,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X30))
      | k9_subset_1(X30,X31,X32) = k3_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_24,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k3_subset_1(X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & ~ r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_26,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X27))
      | m1_subset_1(k9_subset_1(X27,X28,X29),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_33,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4))))
    | ~ r2_hidden(X1,k4_xboole_0(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( k3_subset_1(esk3_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k9_subset_1(esk3_0,X1,esk5_0) = k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),k3_subset_1(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k3_subset_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,esk5_0))) = k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:13:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.12/0.37  # and selection function SelectVGNonCR.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.12/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 0.12/0.37  fof(t42_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 0.12/0.37  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.12/0.37  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.12/0.37  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.12/0.37  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.37  cnf(c_0_10, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_12, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  fof(c_0_13, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  fof(c_0_16, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|r1_tarski(k4_xboole_0(X22,X21),k4_xboole_0(X22,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 0.12/0.37  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_18, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)|r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  fof(c_0_19, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t42_subset_1])).
% 0.12/0.37  fof(c_0_20, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X30))|k9_subset_1(X30,X31,X32)=k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.37  fof(c_0_24, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k3_subset_1(X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.12/0.37  fof(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&~r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.12/0.37  cnf(c_0_26, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_27, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_21, c_0_11])).
% 0.12/0.37  cnf(c_0_28, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_29, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.37  cnf(c_0_30, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  fof(c_0_32, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(X27))|m1_subset_1(k9_subset_1(X27,X28,X29),k1_zfmisc_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.12/0.37  cnf(c_0_33, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_26, c_0_11])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_36, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4))))|~r2_hidden(X1,k4_xboole_0(X2,X4))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (~r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k3_subset_1(esk3_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.37  cnf(c_0_39, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (k9_subset_1(esk3_0,X1,esk5_0)=k4_xboole_0(X1,k4_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.37  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (~r1_tarski(k4_xboole_0(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (m1_subset_1(k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_34])])).
% 0.12/0.37  cnf(c_0_44, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_41, c_0_15])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (~r1_tarski(k4_xboole_0(esk3_0,esk4_0),k3_subset_1(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))))), inference(rw,[status(thm)],[c_0_42, c_0_40])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (k3_subset_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))=k4_xboole_0(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))), inference(spm,[status(thm)],[c_0_30, c_0_43])).
% 0.12/0.37  cnf(c_0_47, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_17, c_0_44])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (~r1_tarski(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.37  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_22, c_0_47])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 51
% 0.12/0.37  # Proof object clause steps            : 34
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 14
% 0.12/0.37  # Proof object clause conjectures      : 11
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 13
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 14
% 0.12/0.37  # Proof object simplifying inferences  : 10
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 17
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 16
% 0.12/0.37  # Processed clauses                    : 78
% 0.12/0.37  # ...of these trivial                  : 4
% 0.12/0.37  # ...subsumed                          : 5
% 0.12/0.37  # ...remaining for further processing  : 69
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 1
% 0.12/0.37  # Backward-rewritten                   : 4
% 0.12/0.37  # Generated clauses                    : 120
% 0.12/0.37  # ...of the previous two non-trivial   : 113
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 113
% 0.12/0.37  # Factorizations                       : 4
% 0.12/0.37  # Equation resolutions                 : 3
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 48
% 0.12/0.37  #    Positive orientable unit clauses  : 21
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 27
% 0.12/0.37  # Current number of unprocessed clauses: 67
% 0.12/0.37  # ...number of literals in the above   : 119
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 22
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 98
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 69
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.12/0.37  # Unit Clause-clause subsumption calls : 32
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 35
% 0.12/0.37  # BW rewrite match successes           : 4
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3620
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

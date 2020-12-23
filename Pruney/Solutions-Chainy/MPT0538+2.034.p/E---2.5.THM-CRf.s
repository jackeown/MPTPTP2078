%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  50 expanded)
%              Number of clauses        :   12 (  25 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 154 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t138_relat_1,conjecture,(
    ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

fof(c_0_5,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X14,X10)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X13,X14),X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(X16,X10)
        | ~ r2_hidden(k4_tarski(X15,X16),X11)
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | ~ r2_hidden(esk2_3(X10,X11,X12),X10)
        | ~ r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_3(X10,X11,X12),X10)
        | r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)
        | r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)
        | X12 = k8_relat_1(X10,X11)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X19,X20,X23,X25,X26] :
      ( ( ~ v1_relat_1(X19)
        | ~ r2_hidden(X20,X19)
        | X20 = k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)) )
      & ( r2_hidden(esk5_1(X23),X23)
        | v1_relat_1(X23) )
      & ( esk5_1(X23) != k4_tarski(X25,X26)
        | v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X1 = k8_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X3)
    | r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X1)
    | r2_hidden(esk5_1(X3),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t138_relat_1])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( X1 = k8_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X1)
    | r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X3)
    | r2_hidden(esk5_1(X1),X1)
    | r2_hidden(esk5_1(X3),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11])).

fof(c_0_18,negated_conjecture,(
    k8_relat_1(esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( k8_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_3(X1,X2,k1_xboole_0),esk2_3(X1,X2,k1_xboole_0)),X2)
    | r2_hidden(esk5_1(X2),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k8_relat_1(esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_19]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:57:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.19/0.40  # and selection function SelectCQIArNXTEqFirst.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.051 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.40  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 0.19/0.40  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.19/0.40  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.19/0.40  fof(t138_relat_1, conjecture, ![X1]:k8_relat_1(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 0.19/0.40  fof(c_0_5, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.40  fof(c_0_6, plain, ![X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X14,X10)|~r2_hidden(k4_tarski(X13,X14),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(X13,X14),X11)|~r2_hidden(k4_tarski(X13,X14),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11)))&(~r2_hidden(X16,X10)|~r2_hidden(k4_tarski(X15,X16),X11)|r2_hidden(k4_tarski(X15,X16),X12)|X12!=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11)))&((~r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|(~r2_hidden(esk2_3(X10,X11,X12),X10)|~r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11))|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&((r2_hidden(esk2_3(X10,X11,X12),X10)|r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X11)|r2_hidden(k4_tarski(esk1_3(X10,X11,X12),esk2_3(X10,X11,X12)),X12)|X12=k8_relat_1(X10,X11)|~v1_relat_1(X12)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.19/0.40  fof(c_0_7, plain, ![X19, X20, X23, X25, X26]:((~v1_relat_1(X19)|(~r2_hidden(X20,X19)|X20=k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20))))&((r2_hidden(esk5_1(X23),X23)|v1_relat_1(X23))&(esk5_1(X23)!=k4_tarski(X25,X26)|v1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.19/0.40  fof(c_0_8, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.19/0.40  cnf(c_0_9, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.40  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)|X3=k8_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_11, plain, (r2_hidden(esk5_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_12, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_13, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_14, plain, (X1=k8_relat_1(X2,X3)|r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X3)|r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X1)|r2_hidden(esk5_1(X3),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.40  fof(c_0_15, negated_conjecture, ~(![X1]:k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t138_relat_1])).
% 0.19/0.40  cnf(c_0_16, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.40  cnf(c_0_17, plain, (X1=k8_relat_1(X2,X3)|r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X1)|r2_hidden(k4_tarski(esk1_3(X2,X3,X1),esk2_3(X2,X3,X1)),X3)|r2_hidden(esk5_1(X1),X1)|r2_hidden(esk5_1(X3),X3)), inference(spm,[status(thm)],[c_0_14, c_0_11])).
% 0.19/0.40  fof(c_0_18, negated_conjecture, k8_relat_1(esk6_0,k1_xboole_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.40  cnf(c_0_19, plain, (k8_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk1_3(X1,X2,k1_xboole_0),esk2_3(X1,X2,k1_xboole_0)),X2)|r2_hidden(esk5_1(X2),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_16])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (k8_relat_1(esk6_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_21, plain, (k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_19]), c_0_16])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 23
% 0.19/0.40  # Proof object clause steps            : 12
% 0.19/0.40  # Proof object formula steps           : 11
% 0.19/0.40  # Proof object conjectures             : 5
% 0.19/0.40  # Proof object clause conjectures      : 2
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 5
% 0.19/0.40  # Proof object initial formulas used   : 5
% 0.19/0.40  # Proof object generating inferences   : 5
% 0.19/0.40  # Proof object simplifying inferences  : 5
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 5
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 14
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 14
% 0.19/0.40  # Processed clauses                    : 63
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 10
% 0.19/0.40  # ...remaining for further processing  : 53
% 0.19/0.40  # Other redundant clauses eliminated   : 5
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 4
% 0.19/0.40  # Generated clauses                    : 71
% 0.19/0.40  # ...of the previous two non-trivial   : 60
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 62
% 0.19/0.40  # Factorizations                       : 4
% 0.19/0.40  # Equation resolutions                 : 5
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 30
% 0.19/0.40  #    Positive orientable unit clauses  : 3
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 25
% 0.19/0.40  # Current number of unprocessed clauses: 25
% 0.19/0.40  # ...number of literals in the above   : 128
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 18
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 276
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 72
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.40  # Unit Clause-clause subsumption calls : 23
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 3
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 2838
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.054 s
% 0.19/0.40  # System time              : 0.007 s
% 0.19/0.40  # Total time               : 0.061 s
% 0.19/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

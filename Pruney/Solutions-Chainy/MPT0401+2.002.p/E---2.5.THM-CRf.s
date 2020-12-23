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
% DateTime   : Thu Dec  3 10:47:31 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of clauses        :   22 (  23 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 120 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_setfam_1(X2,k1_tarski(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t18_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(t24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_setfam_1(X2,k1_tarski(X1))
       => ! [X3] :
            ( r2_hidden(X3,X2)
           => r1_tarski(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t24_setfam_1])).

fof(c_0_9,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | r1_tarski(X26,k3_tarski(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_10,negated_conjecture,
    ( r1_setfam_1(esk4_0,k1_tarski(esk3_0))
    & r2_hidden(esk5_0,esk4_0)
    & ~ r1_tarski(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X24,X25] :
      ( ( ~ r1_tarski(k1_tarski(X24),X25)
        | r2_hidden(X24,X25) )
      & ( ~ r2_hidden(X24,X25)
        | r1_tarski(k1_tarski(X24),X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X30,X31] :
      ( ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(k3_tarski(X30),X31) )
      & ( ~ r1_tarski(esk2_2(X30,X31),X31)
        | r1_tarski(k3_tarski(X30),X31) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X33,X34] :
      ( ~ r1_setfam_1(X33,X34)
      | r1_tarski(k3_tarski(X33),k3_tarski(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_setfam_1])])).

fof(c_0_17,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(k1_tarski(X28),k1_tarski(X29))
      | X28 = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_zfmisc_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk5_0,k3_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_setfam_1(esk4_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_tarski(esk2_2(X1,X2)),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k3_tarski(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k3_tarski(esk4_0),k3_tarski(k1_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( esk2_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k3_tarski(k1_tarski(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk5_0,k3_tarski(k1_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_tarski(k1_tarski(X1)),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k3_tarski(k1_tarski(esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_tarski(k1_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.63  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.47/0.63  # and selection function SelectDivPreferIntoLits.
% 0.47/0.63  #
% 0.47/0.63  # Preprocessing time       : 0.028 s
% 0.47/0.63  # Presaturation interreduction done
% 0.47/0.63  
% 0.47/0.63  # Proof found!
% 0.47/0.63  # SZS status Theorem
% 0.47/0.63  # SZS output start CNFRefutation
% 0.47/0.63  fof(t24_setfam_1, conjecture, ![X1, X2]:(r1_setfam_1(X2,k1_tarski(X1))=>![X3]:(r2_hidden(X3,X2)=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 0.47/0.63  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.47/0.63  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.47/0.63  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.47/0.63  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.47/0.63  fof(t18_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 0.47/0.63  fof(t24_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 0.47/0.63  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.63  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(r1_setfam_1(X2,k1_tarski(X1))=>![X3]:(r2_hidden(X3,X2)=>r1_tarski(X3,X1)))), inference(assume_negation,[status(cth)],[t24_setfam_1])).
% 0.47/0.63  fof(c_0_9, plain, ![X26, X27]:(~r2_hidden(X26,X27)|r1_tarski(X26,k3_tarski(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.47/0.63  fof(c_0_10, negated_conjecture, (r1_setfam_1(esk4_0,k1_tarski(esk3_0))&(r2_hidden(esk5_0,esk4_0)&~r1_tarski(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.47/0.63  fof(c_0_11, plain, ![X24, X25]:((~r1_tarski(k1_tarski(X24),X25)|r2_hidden(X24,X25))&(~r2_hidden(X24,X25)|r1_tarski(k1_tarski(X24),X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.47/0.63  fof(c_0_12, plain, ![X30, X31]:((r2_hidden(esk2_2(X30,X31),X30)|r1_tarski(k3_tarski(X30),X31))&(~r1_tarski(esk2_2(X30,X31),X31)|r1_tarski(k3_tarski(X30),X31))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.47/0.63  fof(c_0_13, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X13,X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.47/0.63  cnf(c_0_14, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.47/0.63  cnf(c_0_15, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.63  fof(c_0_16, plain, ![X33, X34]:(~r1_setfam_1(X33,X34)|r1_tarski(k3_tarski(X33),k3_tarski(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_setfam_1])])).
% 0.47/0.63  fof(c_0_17, plain, ![X28, X29]:(~r1_tarski(k1_tarski(X28),k1_tarski(X29))|X28=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_zfmisc_1])])).
% 0.47/0.63  cnf(c_0_18, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.63  cnf(c_0_19, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.63  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.63  cnf(c_0_21, negated_conjecture, (r1_tarski(esk5_0,k3_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.47/0.63  cnf(c_0_22, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.63  cnf(c_0_23, negated_conjecture, (r1_setfam_1(esk4_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.63  cnf(c_0_24, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.63  cnf(c_0_25, plain, (r1_tarski(k1_tarski(esk2_2(X1,X2)),X1)|r1_tarski(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.47/0.63  fof(c_0_26, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.63  cnf(c_0_27, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(k3_tarski(esk4_0),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.47/0.63  cnf(c_0_28, negated_conjecture, (r1_tarski(k3_tarski(esk4_0),k3_tarski(k1_tarski(esk3_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.47/0.63  cnf(c_0_29, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.63  cnf(c_0_30, plain, (esk2_2(k1_tarski(X1),X2)=X1|r1_tarski(k3_tarski(k1_tarski(X1)),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.47/0.63  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.63  cnf(c_0_32, negated_conjecture, (r1_tarski(esk5_0,k3_tarski(k1_tarski(esk3_0)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.47/0.63  cnf(c_0_33, plain, (r1_tarski(k3_tarski(k1_tarski(X1)),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.47/0.63  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.47/0.63  cnf(c_0_35, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(k3_tarski(k1_tarski(esk3_0)),X1)), inference(spm,[status(thm)],[c_0_20, c_0_32])).
% 0.47/0.63  cnf(c_0_36, plain, (r1_tarski(k3_tarski(k1_tarski(X1)),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.47/0.63  cnf(c_0_37, negated_conjecture, (~r1_tarski(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.63  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), ['proof']).
% 0.47/0.63  # SZS output end CNFRefutation
% 0.47/0.63  # Proof object total steps             : 39
% 0.47/0.63  # Proof object clause steps            : 22
% 0.47/0.63  # Proof object formula steps           : 17
% 0.47/0.63  # Proof object conjectures             : 12
% 0.47/0.63  # Proof object clause conjectures      : 9
% 0.47/0.63  # Proof object formula conjectures     : 3
% 0.47/0.63  # Proof object initial clauses used    : 11
% 0.47/0.63  # Proof object initial formulas used   : 8
% 0.47/0.63  # Proof object generating inferences   : 10
% 0.47/0.63  # Proof object simplifying inferences  : 2
% 0.47/0.63  # Training examples: 0 positive, 0 negative
% 0.47/0.63  # Parsed axioms                        : 13
% 0.47/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.63  # Initial clauses                      : 21
% 0.47/0.63  # Removed in clause preprocessing      : 0
% 0.47/0.63  # Initial clauses in saturation        : 21
% 0.47/0.63  # Processed clauses                    : 2538
% 0.47/0.63  # ...of these trivial                  : 146
% 0.47/0.63  # ...subsumed                          : 1712
% 0.47/0.63  # ...remaining for further processing  : 680
% 0.47/0.63  # Other redundant clauses eliminated   : 2
% 0.47/0.63  # Clauses deleted for lack of memory   : 0
% 0.47/0.63  # Backward-subsumed                    : 18
% 0.47/0.63  # Backward-rewritten                   : 31
% 0.47/0.63  # Generated clauses                    : 27641
% 0.47/0.63  # ...of the previous two non-trivial   : 21047
% 0.47/0.63  # Contextual simplify-reflections      : 1
% 0.47/0.63  # Paramodulations                      : 27639
% 0.47/0.63  # Factorizations                       : 0
% 0.47/0.63  # Equation resolutions                 : 2
% 0.47/0.63  # Propositional unsat checks           : 0
% 0.47/0.63  #    Propositional check models        : 0
% 0.47/0.63  #    Propositional check unsatisfiable : 0
% 0.47/0.63  #    Propositional clauses             : 0
% 0.47/0.63  #    Propositional clauses after purity: 0
% 0.47/0.63  #    Propositional unsat core size     : 0
% 0.47/0.63  #    Propositional preprocessing time  : 0.000
% 0.47/0.63  #    Propositional encoding time       : 0.000
% 0.47/0.63  #    Propositional solver time         : 0.000
% 0.47/0.63  #    Success case prop preproc time    : 0.000
% 0.47/0.63  #    Success case prop encoding time   : 0.000
% 0.47/0.63  #    Success case prop solver time     : 0.000
% 0.47/0.63  # Current number of processed clauses  : 609
% 0.47/0.63  #    Positive orientable unit clauses  : 311
% 0.47/0.63  #    Positive unorientable unit clauses: 0
% 0.47/0.63  #    Negative unit clauses             : 1
% 0.47/0.63  #    Non-unit-clauses                  : 297
% 0.47/0.63  # Current number of unprocessed clauses: 18440
% 0.47/0.63  # ...number of literals in the above   : 30946
% 0.47/0.63  # Current number of archived formulas  : 0
% 0.47/0.63  # Current number of archived clauses   : 69
% 0.47/0.63  # Clause-clause subsumption calls (NU) : 30598
% 0.47/0.63  # Rec. Clause-clause subsumption calls : 23864
% 0.47/0.63  # Non-unit clause-clause subsumptions  : 1731
% 0.47/0.63  # Unit Clause-clause subsumption calls : 486
% 0.47/0.63  # Rewrite failures with RHS unbound    : 0
% 0.47/0.63  # BW rewrite match attempts            : 701
% 0.47/0.63  # BW rewrite match successes           : 27
% 0.47/0.63  # Condensation attempts                : 0
% 0.47/0.63  # Condensation successes               : 0
% 0.47/0.63  # Termbank termtop insertions          : 481627
% 0.47/0.64  
% 0.47/0.64  # -------------------------------------------------
% 0.47/0.64  # User time                : 0.275 s
% 0.47/0.64  # System time              : 0.016 s
% 0.47/0.64  # Total time               : 0.291 s
% 0.47/0.64  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

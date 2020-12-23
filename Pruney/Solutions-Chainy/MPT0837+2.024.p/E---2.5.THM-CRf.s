%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:18 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  96 expanded)
%              Number of clauses        :   22 (  42 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 423 expanded)
%              Number of equality atoms :   11 (  46 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
             => ! [X4] :
                  ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                <=> ? [X5] :
                      ( m1_subset_1(X5,X2)
                      & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
               => ! [X4] :
                    ( r2_hidden(X4,k2_relset_1(X2,X1,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X5,X4),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_relset_1])).

fof(c_0_7,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_8,negated_conjecture,(
    ! [X33] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))
      & ( ~ r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0))
        | ~ m1_subset_1(X33,esk5_0)
        | ~ r2_hidden(k4_tarski(X33,esk7_0),esk6_0) )
      & ( m1_subset_1(esk8_0,esk5_0)
        | r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0)) )
      & ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)
        | r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(esk1_3(X15,X16,X17),X17),X15)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(esk2_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk2_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) )
      & ( r2_hidden(esk2_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk3_2(X21,X22),esk2_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | ~ r2_hidden(X14,X13)
      | r2_hidden(X14,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_11,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9] :
      ( ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X7,X9)
        | r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0))
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( k2_relset_1(esk5_0,esk4_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)
    | r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk4_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0)
    | ~ r2_hidden(esk7_0,k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk7_0,k2_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_17]),c_0_19])).

fof(c_0_25,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X11,X10)
        | r2_hidden(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ r2_hidden(X11,X10)
        | m1_subset_1(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ m1_subset_1(X11,X10)
        | v1_xboole_0(X11)
        | ~ v1_xboole_0(X10) )
      & ( ~ v1_xboole_0(X11)
        | m1_subset_1(X11,X10)
        | ~ v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,k2_relat_1(esk6_0),X1),esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk6_0,k2_relat_1(esk6_0),esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_24])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk1_3(esk6_0,k2_relat_1(esk6_0),X1),esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:47:14 EST 2020
% 0.18/0.32  % CPUTime    : 
% 0.18/0.32  # Version: 2.5pre002
% 0.18/0.32  # No SInE strategy applied
% 0.18/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DN
% 0.18/0.34  # and selection function PSelectComplexExceptRRHorn.
% 0.18/0.34  #
% 0.18/0.34  # Preprocessing time       : 0.013 s
% 0.18/0.34  # Presaturation interreduction done
% 0.18/0.34  
% 0.18/0.34  # Proof found!
% 0.18/0.34  # SZS status Theorem
% 0.18/0.34  # SZS output start CNFRefutation
% 0.18/0.34  fof(t48_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 0.18/0.34  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.18/0.34  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.18/0.34  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.18/0.34  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.18/0.34  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.18/0.34  fof(c_0_6, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>![X4]:(r2_hidden(X4,k2_relset_1(X2,X1,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X5,X4),X3))))))), inference(assume_negation,[status(cth)],[t48_relset_1])).
% 0.18/0.34  fof(c_0_7, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_relset_1(X26,X27,X28)=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.18/0.34  fof(c_0_8, negated_conjecture, ![X33]:(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))&((~r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0))|(~m1_subset_1(X33,esk5_0)|~r2_hidden(k4_tarski(X33,esk7_0),esk6_0)))&((m1_subset_1(esk8_0,esk5_0)|r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0)))&(r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)|r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).
% 0.18/0.34  fof(c_0_9, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:(((~r2_hidden(X17,X16)|r2_hidden(k4_tarski(esk1_3(X15,X16,X17),X17),X15)|X16!=k2_relat_1(X15))&(~r2_hidden(k4_tarski(X20,X19),X15)|r2_hidden(X19,X16)|X16!=k2_relat_1(X15)))&((~r2_hidden(esk2_2(X21,X22),X22)|~r2_hidden(k4_tarski(X24,esk2_2(X21,X22)),X21)|X22=k2_relat_1(X21))&(r2_hidden(esk2_2(X21,X22),X22)|r2_hidden(k4_tarski(esk3_2(X21,X22),esk2_2(X21,X22)),X21)|X22=k2_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.18/0.34  fof(c_0_10, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|(~r2_hidden(X14,X13)|r2_hidden(X14,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.18/0.34  cnf(c_0_11, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_13, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.34  fof(c_0_14, plain, ![X6, X7, X8, X9]:(((r2_hidden(X6,X8)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))&(r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9))))&(~r2_hidden(X6,X8)|~r2_hidden(X7,X9)|r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.18/0.34  cnf(c_0_15, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.34  cnf(c_0_16, negated_conjecture, (~r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0))|~m1_subset_1(X1,esk5_0)|~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_17, negated_conjecture, (k2_relset_1(esk5_0,esk4_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.18/0.34  cnf(c_0_18, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)|r2_hidden(esk7_0,k2_relset_1(esk5_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_19, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_13])).
% 0.18/0.34  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.34  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk4_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_15, c_0_12])).
% 0.18/0.34  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.34  cnf(c_0_23, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)|~r2_hidden(esk7_0,k2_relat_1(esk6_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.34  cnf(c_0_24, negated_conjecture, (r2_hidden(esk7_0,k2_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_17]), c_0_19])).
% 0.18/0.34  fof(c_0_25, plain, ![X10, X11]:(((~m1_subset_1(X11,X10)|r2_hidden(X11,X10)|v1_xboole_0(X10))&(~r2_hidden(X11,X10)|m1_subset_1(X11,X10)|v1_xboole_0(X10)))&((~m1_subset_1(X11,X10)|v1_xboole_0(X11)|~v1_xboole_0(X10))&(~v1_xboole_0(X11)|m1_subset_1(X11,X10)|~v1_xboole_0(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.18/0.34  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X1,X2),esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.34  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_22])).
% 0.18/0.34  cnf(c_0_28, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])])).
% 0.18/0.34  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.34  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_3(esk6_0,k2_relat_1(esk6_0),X1),esk5_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.34  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_32, negated_conjecture, (~m1_subset_1(esk1_3(esk6_0,k2_relat_1(esk6_0),esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_24])])).
% 0.18/0.34  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk1_3(esk6_0,k2_relat_1(esk6_0),X1),esk5_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.18/0.34  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24])]), ['proof']).
% 0.18/0.34  # SZS output end CNFRefutation
% 0.18/0.34  # Proof object total steps             : 35
% 0.18/0.34  # Proof object clause steps            : 22
% 0.18/0.34  # Proof object formula steps           : 13
% 0.18/0.34  # Proof object conjectures             : 17
% 0.18/0.34  # Proof object clause conjectures      : 14
% 0.18/0.34  # Proof object formula conjectures     : 3
% 0.18/0.34  # Proof object initial clauses used    : 10
% 0.18/0.34  # Proof object initial formulas used   : 6
% 0.18/0.34  # Proof object generating inferences   : 7
% 0.18/0.34  # Proof object simplifying inferences  : 12
% 0.18/0.34  # Training examples: 0 positive, 0 negative
% 0.18/0.34  # Parsed axioms                        : 6
% 0.18/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.34  # Initial clauses                      : 19
% 0.18/0.34  # Removed in clause preprocessing      : 0
% 0.18/0.34  # Initial clauses in saturation        : 19
% 0.18/0.34  # Processed clauses                    : 100
% 0.18/0.34  # ...of these trivial                  : 0
% 0.18/0.34  # ...subsumed                          : 5
% 0.18/0.34  # ...remaining for further processing  : 95
% 0.18/0.34  # Other redundant clauses eliminated   : 2
% 0.18/0.34  # Clauses deleted for lack of memory   : 0
% 0.18/0.34  # Backward-subsumed                    : 2
% 0.18/0.34  # Backward-rewritten                   : 5
% 0.18/0.34  # Generated clauses                    : 224
% 0.18/0.34  # ...of the previous two non-trivial   : 206
% 0.18/0.34  # Contextual simplify-reflections      : 1
% 0.18/0.34  # Paramodulations                      : 222
% 0.18/0.34  # Factorizations                       : 0
% 0.18/0.34  # Equation resolutions                 : 2
% 0.18/0.34  # Propositional unsat checks           : 0
% 0.18/0.34  #    Propositional check models        : 0
% 0.18/0.34  #    Propositional check unsatisfiable : 0
% 0.18/0.34  #    Propositional clauses             : 0
% 0.18/0.34  #    Propositional clauses after purity: 0
% 0.18/0.34  #    Propositional unsat core size     : 0
% 0.18/0.34  #    Propositional preprocessing time  : 0.000
% 0.18/0.34  #    Propositional encoding time       : 0.000
% 0.18/0.34  #    Propositional solver time         : 0.000
% 0.18/0.34  #    Success case prop preproc time    : 0.000
% 0.18/0.34  #    Success case prop encoding time   : 0.000
% 0.18/0.34  #    Success case prop solver time     : 0.000
% 0.18/0.34  # Current number of processed clauses  : 67
% 0.18/0.34  #    Positive orientable unit clauses  : 16
% 0.18/0.34  #    Positive unorientable unit clauses: 0
% 0.18/0.34  #    Negative unit clauses             : 3
% 0.18/0.34  #    Non-unit-clauses                  : 48
% 0.18/0.34  # Current number of unprocessed clauses: 136
% 0.18/0.34  # ...number of literals in the above   : 335
% 0.18/0.34  # Current number of archived formulas  : 0
% 0.18/0.34  # Current number of archived clauses   : 26
% 0.18/0.34  # Clause-clause subsumption calls (NU) : 198
% 0.18/0.34  # Rec. Clause-clause subsumption calls : 152
% 0.18/0.34  # Non-unit clause-clause subsumptions  : 6
% 0.18/0.34  # Unit Clause-clause subsumption calls : 21
% 0.18/0.34  # Rewrite failures with RHS unbound    : 0
% 0.18/0.34  # BW rewrite match attempts            : 85
% 0.18/0.34  # BW rewrite match successes           : 2
% 0.18/0.34  # Condensation attempts                : 0
% 0.18/0.34  # Condensation successes               : 0
% 0.18/0.34  # Termbank termtop insertions          : 5033
% 0.18/0.34  
% 0.18/0.34  # -------------------------------------------------
% 0.18/0.34  # User time                : 0.018 s
% 0.18/0.34  # System time              : 0.001 s
% 0.18/0.34  # Total time               : 0.020 s
% 0.18/0.34  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

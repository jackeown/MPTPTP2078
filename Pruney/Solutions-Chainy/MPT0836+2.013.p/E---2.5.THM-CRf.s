%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:14 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   40 (  89 expanded)
%              Number of clauses        :   25 (  40 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  126 ( 387 expanded)
%              Number of equality atoms :   11 (  36 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ( r2_hidden(X4,k1_relset_1(X1,X2,X3))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,X2)
                        & r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
               => ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => ( r2_hidden(X4,k1_relset_1(X1,X2,X3))
                    <=> ? [X5] :
                          ( m1_subset_1(X5,X2)
                          & r2_hidden(k4_tarski(X4,X5),X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_relset_1])).

fof(c_0_8,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X38] :
      ( ~ v1_xboole_0(esk5_0)
      & ~ v1_xboole_0(esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & m1_subset_1(esk8_0,esk5_0)
      & ( ~ r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0))
        | ~ m1_subset_1(X38,esk6_0)
        | ~ r2_hidden(k4_tarski(esk8_0,X38),esk7_0) )
      & ( m1_subset_1(esk9_0,esk6_0)
        | r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0)) )
      & ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)
        | r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(X22,esk2_3(X20,X21,X22)),X20)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X24,X25),X20)
        | r2_hidden(X24,X21)
        | X21 != k1_relat_1(X20) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(esk3_2(X26,X27),X29),X26)
        | X27 = k1_relat_1(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk3_2(X26,X27),esk4_2(X26,X27)),X26)
        | X27 = k1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)
    | r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(esk8_0,X1),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r2_hidden(X12,X14)
        | ~ r2_hidden(k4_tarski(X12,X13),k2_zfmisc_1(X14,X15)) )
      & ( r2_hidden(X13,X15)
        | ~ r2_hidden(k4_tarski(X12,X13),k2_zfmisc_1(X14,X15)) )
      & ( ~ r2_hidden(X12,X14)
        | ~ r2_hidden(X13,X15)
        | r2_hidden(k4_tarski(X12,X13),k2_zfmisc_1(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(esk8_0,X1),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_20])])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | m1_subset_1(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(X1,k1_relat_1(X1),esk8_0),esk6_0)
    | ~ r2_hidden(esk8_0,k1_relat_1(X1))
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_3(X1,k1_relat_1(X1),X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk2_3(X1,k1_relat_1(X1),esk8_0),esk6_0)
    | ~ r2_hidden(esk8_0,k1_relat_1(X1))
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_3(esk7_0,k1_relat_1(esk7_0),X1),esk6_0)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_20]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DN
% 0.42/0.61  # and selection function PSelectComplexExceptRRHorn.
% 0.42/0.61  #
% 0.42/0.61  # Preprocessing time       : 0.028 s
% 0.42/0.61  # Presaturation interreduction done
% 0.42/0.61  
% 0.42/0.61  # Proof found!
% 0.42/0.61  # SZS status Theorem
% 0.42/0.61  # SZS output start CNFRefutation
% 0.42/0.61  fof(t47_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,k1_relset_1(X1,X2,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X4,X5),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relset_1)).
% 0.42/0.61  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.42/0.61  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.42/0.61  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.42/0.61  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.42/0.61  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.42/0.61  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.42/0.61  fof(c_0_7, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,k1_relset_1(X1,X2,X3))<=>?[X5]:(m1_subset_1(X5,X2)&r2_hidden(k4_tarski(X4,X5),X3)))))))), inference(assume_negation,[status(cth)],[t47_relset_1])).
% 0.42/0.61  fof(c_0_8, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.42/0.61  fof(c_0_9, negated_conjecture, ![X38]:(~v1_xboole_0(esk5_0)&(~v1_xboole_0(esk6_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))&(m1_subset_1(esk8_0,esk5_0)&((~r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0))|(~m1_subset_1(X38,esk6_0)|~r2_hidden(k4_tarski(esk8_0,X38),esk7_0)))&((m1_subset_1(esk9_0,esk6_0)|r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0)))&(r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)|r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).
% 0.42/0.61  fof(c_0_10, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:(((~r2_hidden(X22,X21)|r2_hidden(k4_tarski(X22,esk2_3(X20,X21,X22)),X20)|X21!=k1_relat_1(X20))&(~r2_hidden(k4_tarski(X24,X25),X20)|r2_hidden(X24,X21)|X21!=k1_relat_1(X20)))&((~r2_hidden(esk3_2(X26,X27),X27)|~r2_hidden(k4_tarski(esk3_2(X26,X27),X29),X26)|X27=k1_relat_1(X26))&(r2_hidden(esk3_2(X26,X27),X27)|r2_hidden(k4_tarski(esk3_2(X26,X27),esk4_2(X26,X27)),X26)|X27=k1_relat_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.42/0.61  cnf(c_0_11, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.42/0.61  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.42/0.61  cnf(c_0_13, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.42/0.61  cnf(c_0_14, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk7_0)|r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.42/0.61  cnf(c_0_15, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.42/0.61  cnf(c_0_16, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_13])).
% 0.42/0.61  fof(c_0_17, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.42/0.61  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.42/0.61  cnf(c_0_19, negated_conjecture, (~r2_hidden(esk8_0,k1_relset_1(esk5_0,esk6_0,esk7_0))|~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(esk8_0,X1),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.42/0.61  cnf(c_0_20, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.42/0.61  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.61  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_18])).
% 0.42/0.61  fof(c_0_23, plain, ![X12, X13, X14, X15]:(((r2_hidden(X12,X14)|~r2_hidden(k4_tarski(X12,X13),k2_zfmisc_1(X14,X15)))&(r2_hidden(X13,X15)|~r2_hidden(k4_tarski(X12,X13),k2_zfmisc_1(X14,X15))))&(~r2_hidden(X12,X14)|~r2_hidden(X13,X15)|r2_hidden(k4_tarski(X12,X13),k2_zfmisc_1(X14,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.42/0.61  fof(c_0_24, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.42/0.61  cnf(c_0_25, negated_conjecture, (~m1_subset_1(X1,esk6_0)|~r2_hidden(k4_tarski(esk8_0,X1),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_15]), c_0_20])])).
% 0.42/0.61  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X3)|~r2_hidden(X1,k1_relat_1(X2))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.42/0.61  fof(c_0_27, plain, ![X16, X17]:(~r2_hidden(X16,X17)|m1_subset_1(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.42/0.61  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.42/0.61  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.42/0.61  cnf(c_0_30, negated_conjecture, (~m1_subset_1(esk2_3(X1,k1_relat_1(X1),esk8_0),esk6_0)|~r2_hidden(esk8_0,k1_relat_1(X1))|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.42/0.61  cnf(c_0_31, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.42/0.61  cnf(c_0_32, plain, (r2_hidden(esk2_3(X1,k1_relat_1(X1),X2),X3)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(X1,k2_zfmisc_1(X4,X3))), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 0.42/0.61  cnf(c_0_33, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_12])).
% 0.42/0.61  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.61  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.42/0.61  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk2_3(X1,k1_relat_1(X1),esk8_0),esk6_0)|~r2_hidden(esk8_0,k1_relat_1(X1))|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.42/0.61  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_3(esk7_0,k1_relat_1(esk7_0),X1),esk6_0)|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.42/0.61  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.42/0.61  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_20]), c_0_38])]), ['proof']).
% 0.42/0.61  # SZS output end CNFRefutation
% 0.42/0.61  # Proof object total steps             : 40
% 0.42/0.61  # Proof object clause steps            : 25
% 0.42/0.61  # Proof object formula steps           : 15
% 0.42/0.61  # Proof object conjectures             : 14
% 0.42/0.61  # Proof object clause conjectures      : 11
% 0.42/0.61  # Proof object formula conjectures     : 3
% 0.42/0.61  # Proof object initial clauses used    : 12
% 0.42/0.61  # Proof object initial formulas used   : 7
% 0.42/0.61  # Proof object generating inferences   : 9
% 0.42/0.61  # Proof object simplifying inferences  : 10
% 0.42/0.61  # Training examples: 0 positive, 0 negative
% 0.42/0.61  # Parsed axioms                        : 7
% 0.42/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.61  # Initial clauses                      : 21
% 0.42/0.61  # Removed in clause preprocessing      : 0
% 0.42/0.61  # Initial clauses in saturation        : 21
% 0.42/0.61  # Processed clauses                    : 942
% 0.42/0.61  # ...of these trivial                  : 18
% 0.42/0.61  # ...subsumed                          : 129
% 0.42/0.61  # ...remaining for further processing  : 795
% 0.42/0.61  # Other redundant clauses eliminated   : 2
% 0.42/0.61  # Clauses deleted for lack of memory   : 0
% 0.42/0.61  # Backward-subsumed                    : 19
% 0.42/0.61  # Backward-rewritten                   : 3
% 0.42/0.61  # Generated clauses                    : 14011
% 0.42/0.61  # ...of the previous two non-trivial   : 12898
% 0.42/0.61  # Contextual simplify-reflections      : 1
% 0.42/0.61  # Paramodulations                      : 13967
% 0.42/0.61  # Factorizations                       : 42
% 0.42/0.61  # Equation resolutions                 : 2
% 0.42/0.61  # Propositional unsat checks           : 0
% 0.42/0.61  #    Propositional check models        : 0
% 0.42/0.61  #    Propositional check unsatisfiable : 0
% 0.42/0.61  #    Propositional clauses             : 0
% 0.42/0.61  #    Propositional clauses after purity: 0
% 0.42/0.61  #    Propositional unsat core size     : 0
% 0.42/0.61  #    Propositional preprocessing time  : 0.000
% 0.42/0.61  #    Propositional encoding time       : 0.000
% 0.42/0.61  #    Propositional solver time         : 0.000
% 0.42/0.61  #    Success case prop preproc time    : 0.000
% 0.42/0.61  #    Success case prop encoding time   : 0.000
% 0.42/0.61  #    Success case prop solver time     : 0.000
% 0.42/0.61  # Current number of processed clauses  : 750
% 0.42/0.61  #    Positive orientable unit clauses  : 283
% 0.42/0.61  #    Positive unorientable unit clauses: 0
% 0.42/0.61  #    Negative unit clauses             : 5
% 0.42/0.61  #    Non-unit-clauses                  : 462
% 0.42/0.61  # Current number of unprocessed clauses: 11919
% 0.42/0.61  # ...number of literals in the above   : 28002
% 0.42/0.61  # Current number of archived formulas  : 0
% 0.42/0.61  # Current number of archived clauses   : 43
% 0.42/0.61  # Clause-clause subsumption calls (NU) : 50069
% 0.42/0.61  # Rec. Clause-clause subsumption calls : 36698
% 0.42/0.61  # Non-unit clause-clause subsumptions  : 130
% 0.42/0.61  # Unit Clause-clause subsumption calls : 129
% 0.42/0.61  # Rewrite failures with RHS unbound    : 0
% 0.42/0.61  # BW rewrite match attempts            : 17266
% 0.42/0.61  # BW rewrite match successes           : 17
% 0.42/0.61  # Condensation attempts                : 0
% 0.42/0.61  # Condensation successes               : 0
% 0.42/0.61  # Termbank termtop insertions          : 268767
% 0.42/0.61  
% 0.42/0.61  # -------------------------------------------------
% 0.42/0.61  # User time                : 0.233 s
% 0.42/0.61  # System time              : 0.020 s
% 0.42/0.61  # Total time               : 0.253 s
% 0.42/0.61  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

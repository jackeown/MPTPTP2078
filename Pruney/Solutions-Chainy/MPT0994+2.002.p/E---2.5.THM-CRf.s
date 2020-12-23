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
% DateTime   : Thu Dec  3 11:03:51 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 270 expanded)
%              Number of clauses        :   24 ( 107 expanded)
%              Number of leaves         :    7 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 (1216 expanded)
%              Number of equality atoms :   37 ( 321 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_funct_2,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( ( v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( r2_hidden(X3,X1)
          & r2_hidden(k1_funct_1(X5,X3),X4) )
       => ( X2 = k1_xboole_0
          | k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3) = k1_funct_1(X5,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_funct_2)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t86_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(redefinition_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_relset_1(X1,X2,X3,X4) = k8_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(t87_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
       => k1_funct_1(k8_relat_1(X2,X3),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ( v1_funct_1(X5)
          & v1_funct_2(X5,X1,X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( r2_hidden(X3,X1)
            & r2_hidden(k1_funct_1(X5,X3),X4) )
         => ( X2 = k1_xboole_0
            | k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3) = k1_funct_1(X5,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_funct_2])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( X8 != k1_funct_1(X6,X7)
        | r2_hidden(k4_tarski(X7,X8),X6)
        | ~ r2_hidden(X7,k1_relat_1(X6))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X8 = k1_funct_1(X6,X7)
        | ~ r2_hidden(X7,k1_relat_1(X6))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X8 != k1_funct_1(X6,X7)
        | X8 = k1_xboole_0
        | r2_hidden(X7,k1_relat_1(X6))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X8 != k1_xboole_0
        | X8 = k1_funct_1(X6,X7)
        | r2_hidden(X7,k1_relat_1(X6))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_9,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk1_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r2_hidden(esk3_0,esk1_0)
    & r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
    & esk2_0 != k1_xboole_0
    & k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(X11,k1_relat_1(X13))
        | ~ r2_hidden(X11,k1_relat_1(k8_relat_1(X12,X13)))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(k1_funct_1(X13,X11),X12)
        | ~ r2_hidden(X11,k1_relat_1(k8_relat_1(X12,X13)))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(X11,k1_relat_1(X13))
        | ~ r2_hidden(k1_funct_1(X13,X11),X12)
        | r2_hidden(X11,k1_relat_1(k8_relat_1(X12,X13)))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_funct_1])])])).

cnf(c_0_15,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k6_relset_1(X20,X21,X22,X23) = k8_relat_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

fof(c_0_19,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ v1_funct_1(X16)
      | ~ r2_hidden(X14,k1_relat_1(k8_relat_1(X15,X16)))
      | k1_funct_1(k8_relat_1(X15,X16),X14) = k1_funct_1(X16,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_funct_1])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X9,X10] :
      ( ( v1_relat_1(k8_relat_1(X9,X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k8_relat_1(X9,X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

cnf(c_0_24,plain,
    ( k1_funct_1(k8_relat_1(X3,X1),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk5_0)))
    | ~ r2_hidden(k1_funct_1(esk5_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17]),c_0_16])])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( k6_relset_1(esk1_0,esk2_0,X1,esk5_0) = k8_relat_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_28,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_funct_1(esk5_0,X2)
    | k1_funct_1(esk5_0,X2) = k1_xboole_0
    | ~ r2_hidden(k1_funct_1(esk5_0,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_17]),c_0_16])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),X3) = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk5_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(k8_relat_1(X1,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_17])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_funct_1(esk5_0,X2)
    | k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_35]),c_0_17]),c_0_16])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_34])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t41_funct_2, conjecture, ![X1, X2, X3, X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((r2_hidden(X3,X1)&r2_hidden(k1_funct_1(X5,X3),X4))=>(X2=k1_xboole_0|k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3)=k1_funct_1(X5,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_funct_2)).
% 0.20/0.38  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.20/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.38  fof(t86_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 0.20/0.38  fof(redefinition_k6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k6_relset_1(X1,X2,X3,X4)=k8_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 0.20/0.38  fof(t87_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))=>k1_funct_1(k8_relat_1(X2,X3),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_1)).
% 0.20/0.38  fof(fc9_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v1_relat_1(k8_relat_1(X1,X2))&v1_funct_1(k8_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_funct_1)).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((r2_hidden(X3,X1)&r2_hidden(k1_funct_1(X5,X3),X4))=>(X2=k1_xboole_0|k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3)=k1_funct_1(X5,X3))))), inference(assume_negation,[status(cth)],[t41_funct_2])).
% 0.20/0.38  fof(c_0_8, plain, ![X6, X7, X8]:(((X8!=k1_funct_1(X6,X7)|r2_hidden(k4_tarski(X7,X8),X6)|~r2_hidden(X7,k1_relat_1(X6))|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(~r2_hidden(k4_tarski(X7,X8),X6)|X8=k1_funct_1(X6,X7)|~r2_hidden(X7,k1_relat_1(X6))|(~v1_relat_1(X6)|~v1_funct_1(X6))))&((X8!=k1_funct_1(X6,X7)|X8=k1_xboole_0|r2_hidden(X7,k1_relat_1(X6))|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(X8!=k1_xboole_0|X8=k1_funct_1(X6,X7)|r2_hidden(X7,k1_relat_1(X6))|(~v1_relat_1(X6)|~v1_funct_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.38  fof(c_0_10, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk1_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((r2_hidden(esk3_0,esk1_0)&r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0))&(esk2_0!=k1_xboole_0&k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.38  cnf(c_0_11, plain, (X1=k1_xboole_0|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_funct_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_12, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_14, plain, ![X11, X12, X13]:(((r2_hidden(X11,k1_relat_1(X13))|~r2_hidden(X11,k1_relat_1(k8_relat_1(X12,X13)))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(r2_hidden(k1_funct_1(X13,X11),X12)|~r2_hidden(X11,k1_relat_1(k8_relat_1(X12,X13)))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(X11,k1_relat_1(X13))|~r2_hidden(k1_funct_1(X13,X11),X12)|r2_hidden(X11,k1_relat_1(k8_relat_1(X12,X13)))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_funct_1])])])).
% 0.20/0.38  cnf(c_0_15, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_18, plain, ![X20, X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k6_relset_1(X20,X21,X22,X23)=k8_relat_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).
% 0.20/0.38  fof(c_0_19, plain, ![X14, X15, X16]:(~v1_relat_1(X16)|~v1_funct_1(X16)|(~r2_hidden(X14,k1_relat_1(k8_relat_1(X15,X16)))|k1_funct_1(k8_relat_1(X15,X16),X14)=k1_funct_1(X16,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_funct_1])])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.20/0.38  cnf(c_0_22, plain, (k6_relset_1(X2,X3,X4,X1)=k8_relat_1(X4,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_23, plain, ![X9, X10]:((v1_relat_1(k8_relat_1(X9,X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k8_relat_1(X9,X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).
% 0.20/0.38  cnf(c_0_24, plain, (k1_funct_1(k8_relat_1(X3,X1),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk5_0)))|~r2_hidden(k1_funct_1(esk5_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_17]), c_0_16])])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (k6_relset_1(esk1_0,esk2_0,X1,esk5_0)=k8_relat_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_13])).
% 0.20/0.38  cnf(c_0_28, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_29, plain, (v1_funct_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_funct_1(esk5_0,X2)|k1_funct_1(esk5_0,X2)=k1_xboole_0|~r2_hidden(k1_funct_1(esk5_0,X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_17]), c_0_16])])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  cnf(c_0_33, plain, (k1_funct_1(k8_relat_1(X1,X2),X3)=k1_xboole_0|r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_28]), c_0_29])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk5_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(k8_relat_1(X1,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_16]), c_0_17])])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_34])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_funct_1(esk5_0,X2)|k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_35]), c_0_17]), c_0_16])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_34])]), c_0_36]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 39
% 0.20/0.38  # Proof object clause steps            : 24
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 18
% 0.20/0.38  # Proof object clause conjectures      : 15
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 11
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 10
% 0.20/0.38  # Proof object simplifying inferences  : 21
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 19
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 19
% 0.20/0.38  # Processed clauses                    : 73
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 71
% 0.20/0.38  # Other redundant clauses eliminated   : 3
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 3
% 0.20/0.38  # Generated clauses                    : 68
% 0.20/0.38  # ...of the previous two non-trivial   : 68
% 0.20/0.38  # Contextual simplify-reflections      : 4
% 0.20/0.38  # Paramodulations                      : 64
% 0.20/0.38  # Factorizations                       : 1
% 0.20/0.38  # Equation resolutions                 : 3
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 47
% 0.20/0.38  #    Positive orientable unit clauses  : 12
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 33
% 0.20/0.38  # Current number of unprocessed clauses: 31
% 0.20/0.38  # ...number of literals in the above   : 130
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 21
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 240
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 114
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.20/0.38  # Unit Clause-clause subsumption calls : 13
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 11
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3240
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.030 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.036 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:52 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 303 expanded)
%              Number of clauses        :   25 ( 118 expanded)
%              Number of leaves         :    8 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 (1282 expanded)
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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ( v1_funct_1(X5)
          & v1_funct_2(X5,X1,X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( r2_hidden(X3,X1)
            & r2_hidden(k1_funct_1(X5,X3),X4) )
         => ( X2 = k1_xboole_0
            | k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3) = k1_funct_1(X5,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_funct_2])).

fof(c_0_9,plain,(
    ! [X10,X11,X12] :
      ( ( X12 != k1_funct_1(X10,X11)
        | r2_hidden(k4_tarski(X11,X12),X10)
        | ~ r2_hidden(X11,k1_relat_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),X10)
        | X12 = k1_funct_1(X10,X11)
        | ~ r2_hidden(X11,k1_relat_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X12 != k1_funct_1(X10,X11)
        | X12 = k1_xboole_0
        | r2_hidden(X11,k1_relat_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X12 != k1_xboole_0
        | X12 = k1_funct_1(X10,X11)
        | r2_hidden(X11,k1_relat_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk1_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r2_hidden(esk3_0,esk1_0)
    & r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
    & esk2_0 != k1_xboole_0
    & k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X8,X9] : v1_relat_1(k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ( r2_hidden(X15,k1_relat_1(X17))
        | ~ r2_hidden(X15,k1_relat_1(k8_relat_1(X16,X17)))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(k1_funct_1(X17,X15),X16)
        | ~ r2_hidden(X15,k1_relat_1(k8_relat_1(X16,X17)))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X15,k1_relat_1(X17))
        | ~ r2_hidden(k1_funct_1(X17,X15),X16)
        | r2_hidden(X15,k1_relat_1(k8_relat_1(X16,X17)))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_funct_1])])])).

cnf(c_0_18,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

fof(c_0_21,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k6_relset_1(X21,X22,X23,X24) = k8_relat_1(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ r2_hidden(X18,k1_relat_1(k8_relat_1(X19,X20)))
      | k1_funct_1(k8_relat_1(X19,X20),X18) = k1_funct_1(X20,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_funct_1])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_25,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ( v1_relat_1(k8_relat_1(X13,X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( v1_funct_1(k8_relat_1(X13,X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

cnf(c_0_27,plain,
    ( k1_funct_1(k8_relat_1(X3,X1),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk5_0)))
    | ~ r2_hidden(k1_funct_1(esk5_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19]),c_0_20])])).

cnf(c_0_29,negated_conjecture,
    ( k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k6_relset_1(esk1_0,esk2_0,X1,esk5_0) = k8_relat_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_31,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_funct_1(esk5_0,X2)
    | k1_funct_1(esk5_0,X2) = k1_xboole_0
    | ~ r2_hidden(k1_funct_1(esk5_0,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_19]),c_0_20])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),X3) = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk5_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(k8_relat_1(X1,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_19]),c_0_20])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_funct_1(esk5_0,X2)
    | k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_38]),c_0_19]),c_0_20])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_37])]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:00:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.12/0.37  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t41_funct_2, conjecture, ![X1, X2, X3, X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((r2_hidden(X3,X1)&r2_hidden(k1_funct_1(X5,X3),X4))=>(X2=k1_xboole_0|k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3)=k1_funct_1(X5,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_funct_2)).
% 0.12/0.37  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.12/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.37  fof(t86_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 0.12/0.37  fof(redefinition_k6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k6_relset_1(X1,X2,X3,X4)=k8_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 0.12/0.37  fof(t87_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))=>k1_funct_1(k8_relat_1(X2,X3),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_1)).
% 0.12/0.37  fof(fc9_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v1_relat_1(k8_relat_1(X1,X2))&v1_funct_1(k8_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_funct_1)).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((r2_hidden(X3,X1)&r2_hidden(k1_funct_1(X5,X3),X4))=>(X2=k1_xboole_0|k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3)=k1_funct_1(X5,X3))))), inference(assume_negation,[status(cth)],[t41_funct_2])).
% 0.12/0.37  fof(c_0_9, plain, ![X10, X11, X12]:(((X12!=k1_funct_1(X10,X11)|r2_hidden(k4_tarski(X11,X12),X10)|~r2_hidden(X11,k1_relat_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(~r2_hidden(k4_tarski(X11,X12),X10)|X12=k1_funct_1(X10,X11)|~r2_hidden(X11,k1_relat_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10))))&((X12!=k1_funct_1(X10,X11)|X12=k1_xboole_0|r2_hidden(X11,k1_relat_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(X12!=k1_xboole_0|X12=k1_funct_1(X10,X11)|r2_hidden(X11,k1_relat_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.12/0.37  fof(c_0_10, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk1_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((r2_hidden(esk3_0,esk1_0)&r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0))&(esk2_0!=k1_xboole_0&k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X8, X9]:v1_relat_1(k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.37  cnf(c_0_13, plain, (X1=k1_xboole_0|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_funct_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_14, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_16, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_17, plain, ![X15, X16, X17]:(((r2_hidden(X15,k1_relat_1(X17))|~r2_hidden(X15,k1_relat_1(k8_relat_1(X16,X17)))|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(r2_hidden(k1_funct_1(X17,X15),X16)|~r2_hidden(X15,k1_relat_1(k8_relat_1(X16,X17)))|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(X15,k1_relat_1(X17))|~r2_hidden(k1_funct_1(X17,X15),X16)|r2_hidden(X15,k1_relat_1(k8_relat_1(X16,X17)))|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_funct_1])])])).
% 0.12/0.37  cnf(c_0_18, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.12/0.37  fof(c_0_21, plain, ![X21, X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k6_relset_1(X21,X22,X23,X24)=k8_relat_1(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).
% 0.12/0.37  fof(c_0_22, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|~v1_funct_1(X20)|(~r2_hidden(X18,k1_relat_1(k8_relat_1(X19,X20)))|k1_funct_1(k8_relat_1(X19,X20),X18)=k1_funct_1(X20,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_funct_1])])).
% 0.12/0.37  cnf(c_0_23, plain, (r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.12/0.37  cnf(c_0_25, plain, (k6_relset_1(X2,X3,X4,X1)=k8_relat_1(X4,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  fof(c_0_26, plain, ![X13, X14]:((v1_relat_1(k8_relat_1(X13,X14))|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(v1_funct_1(k8_relat_1(X13,X14))|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).
% 0.12/0.37  cnf(c_0_27, plain, (k1_funct_1(k8_relat_1(X3,X1),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk5_0)))|~r2_hidden(k1_funct_1(esk5_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19]), c_0_20])])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k6_relset_1(esk1_0,esk2_0,X1,esk5_0)=k8_relat_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_15])).
% 0.12/0.37  cnf(c_0_31, plain, (v1_funct_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_32, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_funct_1(esk5_0,X2)|k1_funct_1(esk5_0,X2)=k1_xboole_0|~r2_hidden(k1_funct_1(esk5_0,X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_19]), c_0_20])])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_36, plain, (k1_funct_1(k8_relat_1(X1,X2),X3)=k1_xboole_0|r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_31]), c_0_32])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk5_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(k8_relat_1(X1,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_19]), c_0_20])])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_37])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_funct_1(esk5_0,X2)|k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_38]), c_0_19]), c_0_20])])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_37])]), c_0_39]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 42
% 0.12/0.37  # Proof object clause steps            : 25
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 18
% 0.12/0.37  # Proof object clause conjectures      : 15
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 12
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 10
% 0.12/0.37  # Proof object simplifying inferences  : 23
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 20
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 20
% 0.12/0.37  # Processed clauses                    : 71
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 69
% 0.12/0.37  # Other redundant clauses eliminated   : 3
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 3
% 0.12/0.37  # Generated clauses                    : 59
% 0.12/0.37  # ...of the previous two non-trivial   : 58
% 0.12/0.37  # Contextual simplify-reflections      : 4
% 0.12/0.37  # Paramodulations                      : 55
% 0.12/0.37  # Factorizations                       : 1
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
% 0.12/0.37  # Current number of processed clauses  : 44
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 29
% 0.12/0.37  # Current number of unprocessed clauses: 25
% 0.12/0.37  # ...number of literals in the above   : 102
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 22
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 138
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 74
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.12/0.37  # Unit Clause-clause subsumption calls : 13
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 11
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2906
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

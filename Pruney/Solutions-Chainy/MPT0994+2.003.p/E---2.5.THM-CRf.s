%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:51 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 (  87 expanded)
%              Number of clauses        :   24 (  33 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 393 expanded)
%              Number of equality atoms :   45 ( 111 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t86_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(t87_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
       => k1_funct_1(k8_relat_1(X2,X3),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(redefinition_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_relset_1(X1,X2,X3,X4) = k8_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

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
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk1_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r2_hidden(esk3_0,esk1_0)
    & r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
    & esk2_0 != k1_xboole_0
    & k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,plain,(
    ! [X8,X9] : v1_relat_1(k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_13,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_funct_2(X25,X23,X24)
        | X23 = k1_relset_1(X23,X24,X25)
        | X24 = k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_relset_1(X23,X24,X25)
        | v1_funct_2(X25,X23,X24)
        | X24 = k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( ~ v1_funct_2(X25,X23,X24)
        | X23 = k1_relset_1(X23,X24,X25)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_relset_1(X23,X24,X25)
        | v1_funct_2(X25,X23,X24)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( ~ v1_funct_2(X25,X23,X24)
        | X25 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X25 != k1_xboole_0
        | v1_funct_2(X25,X23,X24)
        | X23 = k1_xboole_0
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_14,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] :
      ( ( r2_hidden(X10,k1_relat_1(X12))
        | ~ r2_hidden(X10,k1_relat_1(k8_relat_1(X11,X12)))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(k1_funct_1(X12,X10),X11)
        | ~ r2_hidden(X10,k1_relat_1(k8_relat_1(X11,X12)))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X10,k1_relat_1(X12))
        | ~ r2_hidden(k1_funct_1(X12,X10),X11)
        | r2_hidden(X10,k1_relat_1(k8_relat_1(X11,X12)))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_funct_1])])])).

cnf(c_0_19,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk5_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_24,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ r2_hidden(X13,k1_relat_1(k8_relat_1(X14,X15)))
      | k1_funct_1(k8_relat_1(X14,X15),X13) = k1_funct_1(X15,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_funct_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_15])]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_15])).

fof(c_0_29,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k6_relset_1(X19,X20,X21,X22) = k8_relat_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

cnf(c_0_30,plain,
    ( k1_funct_1(k8_relat_1(X3,X1),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk5_0)))
    | ~ r2_hidden(k1_funct_1(esk5_0,X1),X2)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_32,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(k8_relat_1(X1,esk5_0),X2) = k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(k1_funct_1(esk5_0,X2),X1)
    | ~ r2_hidden(X2,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_27]),c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( k6_relset_1(esk1_0,esk2_0,X1,esk5_0) = k8_relat_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(k8_relat_1(X1,esk5_0),esk3_0) = k1_funct_1(esk5_0,esk3_0)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.36  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.019 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t41_funct_2, conjecture, ![X1, X2, X3, X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((r2_hidden(X3,X1)&r2_hidden(k1_funct_1(X5,X3),X4))=>(X2=k1_xboole_0|k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3)=k1_funct_1(X5,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_funct_2)).
% 0.13/0.36  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.36  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.36  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.36  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.36  fof(t86_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 0.13/0.36  fof(t87_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))=>k1_funct_1(k8_relat_1(X2,X3),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 0.13/0.36  fof(redefinition_k6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k6_relset_1(X1,X2,X3,X4)=k8_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 0.13/0.36  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((r2_hidden(X3,X1)&r2_hidden(k1_funct_1(X5,X3),X4))=>(X2=k1_xboole_0|k1_funct_1(k6_relset_1(X1,X2,X4,X5),X3)=k1_funct_1(X5,X3))))), inference(assume_negation,[status(cth)],[t41_funct_2])).
% 0.13/0.36  fof(c_0_9, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.36  fof(c_0_10, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk1_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((r2_hidden(esk3_0,esk1_0)&r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0))&(esk2_0!=k1_xboole_0&k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.13/0.36  fof(c_0_11, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.36  fof(c_0_12, plain, ![X8, X9]:v1_relat_1(k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.36  fof(c_0_13, plain, ![X23, X24, X25]:((((~v1_funct_2(X25,X23,X24)|X23=k1_relset_1(X23,X24,X25)|X24=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X23!=k1_relset_1(X23,X24,X25)|v1_funct_2(X25,X23,X24)|X24=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&((~v1_funct_2(X25,X23,X24)|X23=k1_relset_1(X23,X24,X25)|X23!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X23!=k1_relset_1(X23,X24,X25)|v1_funct_2(X25,X23,X24)|X23!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))))&((~v1_funct_2(X25,X23,X24)|X25=k1_xboole_0|X23=k1_xboole_0|X24!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X25!=k1_xboole_0|v1_funct_2(X25,X23,X24)|X23=k1_xboole_0|X24!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.36  cnf(c_0_14, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_16, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_17, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  fof(c_0_18, plain, ![X10, X11, X12]:(((r2_hidden(X10,k1_relat_1(X12))|~r2_hidden(X10,k1_relat_1(k8_relat_1(X11,X12)))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(r2_hidden(k1_funct_1(X12,X10),X11)|~r2_hidden(X10,k1_relat_1(k8_relat_1(X11,X12)))|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X10,k1_relat_1(X12))|~r2_hidden(k1_funct_1(X12,X10),X11)|r2_hidden(X10,k1_relat_1(k8_relat_1(X11,X12)))|(~v1_relat_1(X12)|~v1_funct_1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_funct_1])])])).
% 0.13/0.36  cnf(c_0_19, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk5_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_21, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.36  cnf(c_0_22, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_23, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.36  fof(c_0_24, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|~v1_funct_1(X15)|(~r2_hidden(X13,k1_relat_1(k8_relat_1(X14,X15)))|k1_funct_1(k8_relat_1(X14,X15),X13)=k1_funct_1(X15,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_funct_1])])).
% 0.13/0.36  cnf(c_0_25, plain, (r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.36  cnf(c_0_26, negated_conjecture, (k1_relat_1(esk5_0)=esk1_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_15])]), c_0_22])).
% 0.13/0.36  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_15])).
% 0.13/0.36  fof(c_0_29, plain, ![X19, X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k6_relset_1(X19,X20,X21,X22)=k8_relat_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).
% 0.13/0.36  cnf(c_0_30, plain, (k1_funct_1(k8_relat_1(X3,X1),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.36  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk5_0)))|~r2_hidden(k1_funct_1(esk5_0,X1),X2)|~r2_hidden(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.13/0.36  cnf(c_0_32, plain, (k6_relset_1(X2,X3,X4,X1)=k8_relat_1(X4,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (k1_funct_1(k8_relat_1(X1,esk5_0),X2)=k1_funct_1(esk5_0,X2)|~r2_hidden(k1_funct_1(esk5_0,X2),X1)|~r2_hidden(X2,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_27]), c_0_28])])).
% 0.13/0.36  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_35, negated_conjecture, (k1_funct_1(k6_relset_1(esk1_0,esk2_0,esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_36, negated_conjecture, (k6_relset_1(esk1_0,esk2_0,X1,esk5_0)=k8_relat_1(X1,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_15])).
% 0.13/0.36  cnf(c_0_37, negated_conjecture, (k1_funct_1(k8_relat_1(X1,esk5_0),esk3_0)=k1_funct_1(esk5_0,esk3_0)|~r2_hidden(k1_funct_1(esk5_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.36  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_39, negated_conjecture, (k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 41
% 0.13/0.36  # Proof object clause steps            : 24
% 0.13/0.36  # Proof object formula steps           : 17
% 0.13/0.36  # Proof object conjectures             : 19
% 0.13/0.36  # Proof object clause conjectures      : 16
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 14
% 0.13/0.36  # Proof object initial formulas used   : 8
% 0.13/0.36  # Proof object generating inferences   : 9
% 0.13/0.36  # Proof object simplifying inferences  : 12
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 8
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 21
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 21
% 0.13/0.36  # Processed clauses                    : 60
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 60
% 0.13/0.36  # Other redundant clauses eliminated   : 5
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 2
% 0.13/0.36  # Generated clauses                    : 27
% 0.13/0.36  # ...of the previous two non-trivial   : 23
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 23
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 5
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 33
% 0.13/0.36  #    Positive orientable unit clauses  : 10
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 2
% 0.13/0.36  #    Non-unit-clauses                  : 21
% 0.13/0.36  # Current number of unprocessed clauses: 4
% 0.13/0.36  # ...number of literals in the above   : 22
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 23
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 136
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 62
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 8
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 2
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 2165
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.021 s
% 0.13/0.36  # System time              : 0.003 s
% 0.13/0.36  # Total time               : 0.025 s
% 0.13/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

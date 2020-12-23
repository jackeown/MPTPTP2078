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
% DateTime   : Thu Dec  3 11:01:10 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 (  72 expanded)
%              Number of clauses        :   22 (  26 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  145 ( 311 expanded)
%              Number of equality atoms :   40 (  68 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t176_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v5_relat_1(X3,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,k1_relat_1(X3))
       => m1_subset_1(k1_funct_1(X3,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r2_hidden(X3,X1)
         => ( X2 = k1_xboole_0
            | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_funct_2])).

fof(c_0_10,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v1_funct_2(X31,X29,X30)
        | X29 = k1_relset_1(X29,X30,X31)
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X29 != k1_relset_1(X29,X30,X31)
        | v1_funct_2(X31,X29,X30)
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ v1_funct_2(X31,X29,X30)
        | X29 = k1_relset_1(X29,X30,X31)
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X29 != k1_relset_1(X29,X30,X31)
        | v1_funct_2(X31,X29,X30)
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ v1_funct_2(X31,X29,X30)
        | X31 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X31 != k1_xboole_0
        | v1_funct_2(X31,X29,X30)
        | X29 = k1_xboole_0
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & r2_hidden(esk5_0,esk3_0)
    & esk4_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk6_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,X11)
      | v1_xboole_0(X11)
      | r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ v5_relat_1(X14,X12)
      | ~ v1_funct_1(X14)
      | ~ r2_hidden(X13,k1_relat_1(X14))
      | m1_subset_1(k1_funct_1(X14,X13),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_funct_1])])).

fof(c_0_14,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_15,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_17,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X24,X26,X27,X28] :
      ( ( r2_hidden(esk2_1(X24),X24)
        | X24 = k1_xboole_0 )
      & ( ~ r2_hidden(X26,X24)
        | esk2_1(X24) != k3_mcart_1(X26,X27,X28)
        | X24 = k1_xboole_0 )
      & ( ~ r2_hidden(X27,X24)
        | esk2_1(X24) != k3_mcart_1(X26,X27,X28)
        | X24 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk6_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( v5_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:30:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t7_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 0.13/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.38  fof(t176_funct_1, axiom, ![X1, X2, X3]:(((v1_relat_1(X3)&v5_relat_1(X3,X1))&v1_funct_1(X3))=>(r2_hidden(X2,k1_relat_1(X3))=>m1_subset_1(k1_funct_1(X3,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 0.13/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2))))), inference(assume_negation,[status(cth)],[t7_funct_2])).
% 0.13/0.38  fof(c_0_10, plain, ![X29, X30, X31]:((((~v1_funct_2(X31,X29,X30)|X29=k1_relset_1(X29,X30,X31)|X30=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X29!=k1_relset_1(X29,X30,X31)|v1_funct_2(X31,X29,X30)|X30=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&((~v1_funct_2(X31,X29,X30)|X29=k1_relset_1(X29,X30,X31)|X29!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X29!=k1_relset_1(X29,X30,X31)|v1_funct_2(X31,X29,X30)|X29!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))))&((~v1_funct_2(X31,X29,X30)|X31=k1_xboole_0|X29=k1_xboole_0|X30!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X31!=k1_xboole_0|v1_funct_2(X31,X29,X30)|X29=k1_xboole_0|X30!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.38  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r2_hidden(esk5_0,esk3_0)&(esk4_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk6_0,esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X10, X11]:(~m1_subset_1(X10,X11)|(v1_xboole_0(X11)|r2_hidden(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.38  fof(c_0_13, plain, ![X12, X13, X14]:(~v1_relat_1(X14)|~v5_relat_1(X14,X12)|~v1_funct_1(X14)|(~r2_hidden(X13,k1_relat_1(X14))|m1_subset_1(k1_funct_1(X14,X13),X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_funct_1])])).
% 0.13/0.38  fof(c_0_14, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.38  fof(c_0_16, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.38  cnf(c_0_17, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_21, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X24, X26, X27, X28]:((r2_hidden(esk2_1(X24),X24)|X24=k1_xboole_0)&((~r2_hidden(X26,X24)|esk2_1(X24)!=k3_mcart_1(X26,X27,X28)|X24=k1_xboole_0)&(~r2_hidden(X27,X24)|esk2_1(X24)!=k3_mcart_1(X26,X27,X28)|X24=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.13/0.38  cnf(c_0_23, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_24, plain, (m1_subset_1(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_25, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_27, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20])).
% 0.13/0.38  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_30, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~r2_hidden(k1_funct_1(esk6_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v5_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_18])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_28])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_38, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_20]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 41
% 0.13/0.38  # Proof object clause steps            : 22
% 0.13/0.38  # Proof object formula steps           : 19
% 0.13/0.38  # Proof object conjectures             : 15
% 0.13/0.38  # Proof object clause conjectures      : 12
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 11
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 23
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 23
% 0.13/0.38  # Processed clauses                    : 41
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 41
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 28
% 0.13/0.38  # ...of the previous two non-trivial   : 23
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 24
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 5
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 37
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 24
% 0.13/0.38  # Current number of unprocessed clauses: 5
% 0.13/0.38  # ...number of literals in the above   : 33
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 0
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 141
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 59
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 17
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1963
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

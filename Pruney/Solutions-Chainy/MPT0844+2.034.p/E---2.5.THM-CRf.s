%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:53 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 (  84 expanded)
%              Number of clauses        :   25 (  35 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 196 expanded)
%              Number of equality atoms :   24 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_xboole_0(X2,X3)
       => k5_relset_1(X3,X1,X4,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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

fof(t34_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( r1_tarski(X2,X3)
       => r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(t33_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
       => ( r1_xboole_0(X2,X3)
         => k5_relset_1(X3,X1,X4,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t55_relset_1])).

fof(c_0_11,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k5_relset_1(X16,X17,X18,X19) = k7_relat_1(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & r1_xboole_0(esk2_0,esk3_0)
    & k5_relset_1(esk3_0,esk1_0,esk4_0,esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_14,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_16,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X28)))
      | ~ r1_tarski(X29,X30)
      | r2_relset_1(X29,X28,k5_relset_1(X29,X28,X31,X30),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_relset_1])])).

cnf(c_0_17,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ r1_xboole_0(X13,X14)
      | k7_relat_1(k7_relat_1(X15,X13),X14) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_relset_1(X2,X3,k5_relset_1(X2,X3,X1,X4),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k5_relset_1(esk3_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X24,X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X26)))
      | m1_subset_1(k5_relset_1(X24,X26,X27,X25),k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_relset_1])])).

cnf(c_0_29,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_32,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ r2_relset_1(X20,X21,X22,X23)
        | X22 = X23
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X22 != X23
        | r2_relset_1(X20,X21,X22,X23)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_relset_1(esk3_0,esk1_0,k7_relat_1(esk4_0,X1),esk4_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( m1_subset_1(k5_relset_1(X2,X3,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk3_0),esk2_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_38,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_relset_1(esk3_0,esk1_0,k7_relat_1(esk4_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_18])])).

cnf(c_0_41,negated_conjecture,
    ( k5_relset_1(esk3_0,esk1_0,esk4_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk4_0,esk3_0),esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_18]),c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( k7_relat_1(esk4_0,esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.13/0.36  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.013 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t55_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_xboole_0(X2,X3)=>k5_relset_1(X3,X1,X4,X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 0.13/0.36  fof(redefinition_k5_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k5_relset_1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 0.13/0.36  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.36  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.36  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.36  fof(t34_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(r1_tarski(X2,X3)=>r2_relset_1(X2,X1,k5_relset_1(X2,X1,X4,X3),X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 0.13/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.36  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 0.13/0.36  fof(t33_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 0.13/0.36  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.13/0.36  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_xboole_0(X2,X3)=>k5_relset_1(X3,X1,X4,X2)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t55_relset_1])).
% 0.13/0.36  fof(c_0_11, plain, ![X16, X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k5_relset_1(X16,X17,X18,X19)=k7_relat_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).
% 0.13/0.36  fof(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))&(r1_xboole_0(esk2_0,esk3_0)&k5_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.36  fof(c_0_13, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.36  fof(c_0_14, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.36  fof(c_0_15, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.36  fof(c_0_16, plain, ![X28, X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X28)))|(~r1_tarski(X29,X30)|r2_relset_1(X29,X28,k5_relset_1(X29,X28,X31,X30),X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_relset_1])])).
% 0.13/0.36  cnf(c_0_17, plain, (k5_relset_1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  fof(c_0_19, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.36  fof(c_0_20, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|(~r1_xboole_0(X13,X14)|k7_relat_1(k7_relat_1(X15,X13),X14)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.13/0.36  cnf(c_0_21, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.36  cnf(c_0_22, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  cnf(c_0_23, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_24, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.36  cnf(c_0_25, plain, (r2_relset_1(X2,X3,k5_relset_1(X2,X3,X1,X4),X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.36  cnf(c_0_26, negated_conjecture, (k5_relset_1(esk3_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.36  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.36  fof(c_0_28, plain, ![X24, X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X26)))|m1_subset_1(k5_relset_1(X24,X26,X27,X25),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_relset_1])])).
% 0.13/0.36  cnf(c_0_29, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.36  cnf(c_0_30, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.36  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.36  fof(c_0_32, plain, ![X20, X21, X22, X23]:((~r2_relset_1(X20,X21,X22,X23)|X22=X23|(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(X22!=X23|r2_relset_1(X20,X21,X22,X23)|(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (r2_relset_1(esk3_0,esk1_0,k7_relat_1(esk4_0,X1),esk4_0)|~r1_tarski(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_26])).
% 0.13/0.36  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.36  cnf(c_0_35, plain, (m1_subset_1(k5_relset_1(X2,X3,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.36  cnf(c_0_36, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk3_0),esk2_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.36  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_18])).
% 0.13/0.36  cnf(c_0_38, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.36  cnf(c_0_39, negated_conjecture, (r2_relset_1(esk3_0,esk1_0,k7_relat_1(esk4_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_18])])).
% 0.13/0.36  cnf(c_0_41, negated_conjecture, (k5_relset_1(esk3_0,esk1_0,esk4_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (k7_relat_1(k7_relat_1(esk4_0,esk3_0),esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.36  cnf(c_0_43, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_18]), c_0_40])])).
% 0.13/0.36  cnf(c_0_44, negated_conjecture, (k7_relat_1(esk4_0,esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_26])).
% 0.13/0.36  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 46
% 0.13/0.36  # Proof object clause steps            : 25
% 0.13/0.36  # Proof object formula steps           : 21
% 0.13/0.36  # Proof object conjectures             : 17
% 0.13/0.36  # Proof object clause conjectures      : 14
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 12
% 0.13/0.36  # Proof object initial formulas used   : 10
% 0.13/0.36  # Proof object generating inferences   : 10
% 0.13/0.36  # Proof object simplifying inferences  : 10
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 10
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 15
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 15
% 0.13/0.36  # Processed clauses                    : 59
% 0.13/0.36  # ...of these trivial                  : 1
% 0.13/0.36  # ...subsumed                          : 3
% 0.13/0.36  # ...remaining for further processing  : 55
% 0.13/0.36  # Other redundant clauses eliminated   : 3
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 3
% 0.13/0.36  # Generated clauses                    : 64
% 0.13/0.36  # ...of the previous two non-trivial   : 53
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 61
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 3
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
% 0.13/0.36  # Current number of processed clauses  : 35
% 0.13/0.36  #    Positive orientable unit clauses  : 14
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 20
% 0.13/0.36  # Current number of unprocessed clauses: 23
% 0.13/0.36  # ...number of literals in the above   : 66
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 17
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 60
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 52
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.36  # Unit Clause-clause subsumption calls : 18
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 4
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 2040
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.015 s
% 0.13/0.36  # System time              : 0.003 s
% 0.13/0.36  # Total time               : 0.017 s
% 0.13/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

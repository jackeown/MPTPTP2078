%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:44 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 122 expanded)
%              Number of clauses        :   25 (  48 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 493 expanded)
%              Number of equality atoms :   75 ( 190 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(t43_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_zfmisc_1(X2) )
           => ( r1_tarski(X1,X2)
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t1_tex_2])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ( X13 = k1_tarski(X12)
        | X13 = k1_xboole_0
        | X13 = k1_tarski(X12)
        | k1_tarski(X12) != k2_xboole_0(X13,X14) )
      & ( X14 = k1_xboole_0
        | X13 = k1_xboole_0
        | X13 = k1_tarski(X12)
        | k1_tarski(X12) != k2_xboole_0(X13,X14) )
      & ( X13 = k1_tarski(X12)
        | X14 = k1_tarski(X12)
        | X13 = k1_tarski(X12)
        | k1_tarski(X12) != k2_xboole_0(X13,X14) )
      & ( X14 = k1_xboole_0
        | X14 = k1_tarski(X12)
        | X13 = k1_tarski(X12)
        | k1_tarski(X12) != k2_xboole_0(X13,X14) )
      & ( X13 = k1_tarski(X12)
        | X13 = k1_xboole_0
        | X14 = k1_tarski(X12)
        | k1_tarski(X12) != k2_xboole_0(X13,X14) )
      & ( X14 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_tarski(X12)
        | k1_tarski(X12) != k2_xboole_0(X13,X14) )
      & ( X13 = k1_tarski(X12)
        | X14 = k1_tarski(X12)
        | X14 = k1_tarski(X12)
        | k1_tarski(X12) != k2_xboole_0(X13,X14) )
      & ( X14 = k1_xboole_0
        | X14 = k1_tarski(X12)
        | X14 = k1_tarski(X12)
        | k1_tarski(X12) != k2_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_11,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & v1_zfmisc_1(esk3_0)
    & r1_tarski(esk2_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_12,plain,(
    ! [X17,X19] :
      ( ( m1_subset_1(esk1_1(X17),X17)
        | ~ v1_zfmisc_1(X17)
        | v1_xboole_0(X17) )
      & ( X17 = k6_domain_1(X17,esk1_1(X17))
        | ~ v1_zfmisc_1(X17)
        | v1_xboole_0(X17) )
      & ( ~ m1_subset_1(X19,X17)
        | X17 != k6_domain_1(X17,X19)
        | v1_zfmisc_1(X17)
        | v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_13,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | k1_tarski(X2) != k2_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,X15)
      | k6_domain_1(X15,X16) = k1_tarski(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_zfmisc_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( X1 = k6_domain_1(X1,esk1_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( v1_xboole_0(X11)
      | ~ r1_tarski(X11,X10)
      | ~ r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | k1_tarski(X2) != k2_xboole_0(X1,X3) ),
    inference(cn,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k6_domain_1(esk3_0,esk1_1(esk3_0)) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_19])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_31,negated_conjecture,
    ( k1_tarski(X1) = esk2_0
    | esk2_0 = k1_xboole_0
    | k1_tarski(X1) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k1_tarski(esk1_1(esk3_0)) = esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | k3_xboole_0(X1,X2) != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % WCLimit    : 600
% 0.12/0.35  % DateTime   : Tue Dec  1 14:15:20 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t1_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.12/0.38  fof(t43_zfmisc_1, axiom, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.12/0.38  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.38  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 0.12/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.12/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.12/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.12/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2)))), inference(assume_negation,[status(cth)],[t1_tex_2])).
% 0.12/0.38  fof(c_0_9, plain, ![X12, X13, X14]:((((X13=k1_tarski(X12)|(X13=k1_xboole_0|(X13=k1_tarski(X12)|k1_tarski(X12)!=k2_xboole_0(X13,X14))))&(X14=k1_xboole_0|(X13=k1_xboole_0|(X13=k1_tarski(X12)|k1_tarski(X12)!=k2_xboole_0(X13,X14)))))&((X13=k1_tarski(X12)|(X14=k1_tarski(X12)|(X13=k1_tarski(X12)|k1_tarski(X12)!=k2_xboole_0(X13,X14))))&(X14=k1_xboole_0|(X14=k1_tarski(X12)|(X13=k1_tarski(X12)|k1_tarski(X12)!=k2_xboole_0(X13,X14))))))&(((X13=k1_tarski(X12)|(X13=k1_xboole_0|(X14=k1_tarski(X12)|k1_tarski(X12)!=k2_xboole_0(X13,X14))))&(X14=k1_xboole_0|(X13=k1_xboole_0|(X14=k1_tarski(X12)|k1_tarski(X12)!=k2_xboole_0(X13,X14)))))&((X13=k1_tarski(X12)|(X14=k1_tarski(X12)|(X14=k1_tarski(X12)|k1_tarski(X12)!=k2_xboole_0(X13,X14))))&(X14=k1_xboole_0|(X14=k1_tarski(X12)|(X14=k1_tarski(X12)|k1_tarski(X12)!=k2_xboole_0(X13,X14))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_zfmisc_1])])])).
% 0.12/0.38  fof(c_0_10, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.38  fof(c_0_11, negated_conjecture, (~v1_xboole_0(esk2_0)&((~v1_xboole_0(esk3_0)&v1_zfmisc_1(esk3_0))&(r1_tarski(esk2_0,esk3_0)&esk2_0!=esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.12/0.38  fof(c_0_12, plain, ![X17, X19]:(((m1_subset_1(esk1_1(X17),X17)|~v1_zfmisc_1(X17)|v1_xboole_0(X17))&(X17=k6_domain_1(X17,esk1_1(X17))|~v1_zfmisc_1(X17)|v1_xboole_0(X17)))&(~m1_subset_1(X19,X17)|X17!=k6_domain_1(X17,X19)|v1_zfmisc_1(X17)|v1_xboole_0(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.12/0.38  cnf(c_0_13, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|X1=k1_tarski(X2)|k1_tarski(X2)!=k2_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_16, plain, ![X15, X16]:(v1_xboole_0(X15)|~m1_subset_1(X16,X15)|k6_domain_1(X15,X16)=k1_tarski(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.12/0.38  cnf(c_0_17, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (v1_zfmisc_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_20, plain, (X1=k6_domain_1(X1,esk1_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  fof(c_0_21, plain, ![X10, X11]:(v1_xboole_0(X11)|(~r1_tarski(X11,X10)|~r1_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.12/0.38  fof(c_0_22, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.12/0.38  cnf(c_0_23, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|k1_tarski(X2)!=k2_xboole_0(X1,X3)), inference(cn,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.38  cnf(c_0_25, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (k6_domain_1(esk3_0,esk1_1(esk3_0))=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_18]), c_0_19])).
% 0.12/0.38  cnf(c_0_28, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  fof(c_0_30, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (k1_tarski(X1)=esk2_0|esk2_0=k1_xboole_0|k1_tarski(X1)!=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (k1_tarski(esk1_1(esk3_0))=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_19])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_34, plain, (v1_xboole_0(X1)|k3_xboole_0(X1,X2)!=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.38  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_38, plain, (v1_xboole_0(k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35])])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[c_0_15, c_0_36])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 42
% 0.12/0.38  # Proof object clause steps            : 25
% 0.12/0.38  # Proof object formula steps           : 17
% 0.12/0.38  # Proof object conjectures             : 17
% 0.12/0.38  # Proof object clause conjectures      : 14
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 13
% 0.12/0.38  # Proof object initial formulas used   : 8
% 0.12/0.38  # Proof object generating inferences   : 9
% 0.12/0.38  # Proof object simplifying inferences  : 10
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 8
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 22
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 22
% 0.12/0.38  # Processed clauses                    : 51
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 5
% 0.12/0.38  # ...remaining for further processing  : 46
% 0.12/0.38  # Other redundant clauses eliminated   : 1
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 5
% 0.12/0.38  # Generated clauses                    : 17
% 0.12/0.38  # ...of the previous two non-trivial   : 16
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 16
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 1
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 24
% 0.12/0.38  #    Positive orientable unit clauses  : 6
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 15
% 0.12/0.38  # Current number of unprocessed clauses: 3
% 0.12/0.38  # ...number of literals in the above   : 7
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 22
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 54
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 46
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.38  # Unit Clause-clause subsumption calls : 23
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 1302
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.028 s
% 0.12/0.38  # System time              : 0.005 s
% 0.12/0.38  # Total time               : 0.032 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

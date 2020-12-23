%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:18 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 141 expanded)
%              Number of clauses        :   33 (  63 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  146 ( 500 expanded)
%              Number of equality atoms :   36 ( 130 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
        <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t22_relset_1])).

fof(c_0_9,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_10,negated_conjecture,(
    ! [X40,X41] :
      ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
      & ( r2_hidden(esk8_0,esk6_0)
        | k1_relset_1(esk6_0,esk5_0,esk7_0) != esk6_0 )
      & ( ~ r2_hidden(k4_tarski(esk8_0,X40),esk7_0)
        | k1_relset_1(esk6_0,esk5_0,esk7_0) != esk6_0 )
      & ( ~ r2_hidden(X41,esk6_0)
        | r2_hidden(k4_tarski(X41,esk9_1(X41)),esk7_0)
        | k1_relset_1(esk6_0,esk5_0,esk7_0) = esk6_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

cnf(c_0_11,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(X18,esk2_3(X16,X17,X18)),X16)
        | X17 != k1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X16)
        | r2_hidden(X20,X17)
        | X17 != k1_relat_1(X16) )
      & ( ~ r2_hidden(esk3_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(esk3_2(X22,X23),X25),X22)
        | X23 = k1_relat_1(X22) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk3_2(X22,X23),esk4_2(X22,X23)),X22)
        | X23 = k1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk9_1(X1)),esk7_0)
    | k1_relset_1(esk6_0,esk5_0,esk7_0) = esk6_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k1_relset_1(esk6_0,esk5_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk6_0
    | r2_hidden(k4_tarski(X1,esk9_1(X1)),esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk8_0,X1),esk7_0)
    | k1_relset_1(esk6_0,esk5_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_0)
    | k1_relset_1(esk6_0,esk5_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_24,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ( ~ v4_relat_1(X15,X14)
        | r1_tarski(k1_relat_1(X15),X14)
        | ~ v1_relat_1(X15) )
      & ( ~ r1_tarski(k1_relat_1(X15),X14)
        | v4_relat_1(X15,X14)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk6_0
    | r2_hidden(k4_tarski(esk1_2(esk6_0,X1),esk9_1(esk1_2(esk6_0,X1))),esk7_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_28,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_29,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(esk6_0,esk5_0,esk7_0) != esk6_0
    | ~ r2_hidden(esk8_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_0)
    | k1_relat_1(esk7_0) != esk6_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_15])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk6_0
    | r2_hidden(esk1_2(esk6_0,X1),k1_relat_1(esk7_0))
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk7_0) != esk6_0
    | ~ r2_hidden(esk8_0,k1_relat_1(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | k1_relat_1(esk7_0) != esk6_0
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk6_0
    | r1_tarski(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v4_relat_1(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_12])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(esk7_0) != esk6_0
    | ~ r1_tarski(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:18:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t22_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 0.18/0.36  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.36  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.18/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.36  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.18/0.36  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.36  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.36  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2))), inference(assume_negation,[status(cth)],[t22_relset_1])).
% 0.18/0.36  fof(c_0_9, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.36  fof(c_0_10, negated_conjecture, ![X40, X41]:(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))&(((r2_hidden(esk8_0,esk6_0)|k1_relset_1(esk6_0,esk5_0,esk7_0)!=esk6_0)&(~r2_hidden(k4_tarski(esk8_0,X40),esk7_0)|k1_relset_1(esk6_0,esk5_0,esk7_0)!=esk6_0))&(~r2_hidden(X41,esk6_0)|r2_hidden(k4_tarski(X41,esk9_1(X41)),esk7_0)|k1_relset_1(esk6_0,esk5_0,esk7_0)=esk6_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 0.18/0.36  cnf(c_0_11, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  fof(c_0_13, plain, ![X16, X17, X18, X20, X21, X22, X23, X25]:(((~r2_hidden(X18,X17)|r2_hidden(k4_tarski(X18,esk2_3(X16,X17,X18)),X16)|X17!=k1_relat_1(X16))&(~r2_hidden(k4_tarski(X20,X21),X16)|r2_hidden(X20,X17)|X17!=k1_relat_1(X16)))&((~r2_hidden(esk3_2(X22,X23),X23)|~r2_hidden(k4_tarski(esk3_2(X22,X23),X25),X22)|X23=k1_relat_1(X22))&(r2_hidden(esk3_2(X22,X23),X23)|r2_hidden(k4_tarski(esk3_2(X22,X23),esk4_2(X22,X23)),X22)|X23=k1_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.18/0.36  cnf(c_0_14, negated_conjecture, (r2_hidden(k4_tarski(X1,esk9_1(X1)),esk7_0)|k1_relset_1(esk6_0,esk5_0,esk7_0)=esk6_0|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (k1_relset_1(esk6_0,esk5_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.18/0.36  fof(c_0_16, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.36  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_18, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (k1_relat_1(esk7_0)=esk6_0|r2_hidden(k4_tarski(X1,esk9_1(X1)),esk7_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.36  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (~r2_hidden(k4_tarski(esk8_0,X1),esk7_0)|k1_relset_1(esk6_0,esk5_0,esk7_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (r2_hidden(esk8_0,esk6_0)|k1_relset_1(esk6_0,esk5_0,esk7_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  fof(c_0_24, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.36  fof(c_0_25, plain, ![X14, X15]:((~v4_relat_1(X15,X14)|r1_tarski(k1_relat_1(X15),X14)|~v1_relat_1(X15))&(~r1_tarski(k1_relat_1(X15),X14)|v4_relat_1(X15,X14)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.18/0.36  cnf(c_0_26, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_18])).
% 0.18/0.36  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk7_0)=esk6_0|r2_hidden(k4_tarski(esk1_2(esk6_0,X1),esk9_1(esk1_2(esk6_0,X1))),esk7_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.36  fof(c_0_28, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.36  fof(c_0_29, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.36  cnf(c_0_30, negated_conjecture, (k1_relset_1(esk6_0,esk5_0,esk7_0)!=esk6_0|~r2_hidden(esk8_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.36  cnf(c_0_31, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (r2_hidden(esk8_0,esk6_0)|k1_relat_1(esk7_0)!=esk6_0), inference(rw,[status(thm)],[c_0_23, c_0_15])).
% 0.18/0.36  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  cnf(c_0_34, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.36  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk7_0)=esk6_0|r2_hidden(esk1_2(esk6_0,X1),k1_relat_1(esk7_0))|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.36  cnf(c_0_37, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.36  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.36  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk7_0)!=esk6_0|~r2_hidden(esk8_0,k1_relat_1(esk7_0))), inference(rw,[status(thm)],[c_0_30, c_0_15])).
% 0.18/0.36  cnf(c_0_40, negated_conjecture, (r2_hidden(esk8_0,X1)|k1_relat_1(esk7_0)!=esk6_0|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.36  cnf(c_0_41, plain, (X1=k1_relat_1(X2)|~v4_relat_1(X2,X1)|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.36  cnf(c_0_42, negated_conjecture, (k1_relat_1(esk7_0)=esk6_0|r1_tarski(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.36  cnf(c_0_43, negated_conjecture, (v4_relat_1(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_12])).
% 0.18/0.36  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_12])).
% 0.18/0.36  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  cnf(c_0_46, negated_conjecture, (k1_relat_1(esk7_0)!=esk6_0|~r1_tarski(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.18/0.36  cnf(c_0_47, negated_conjecture, (k1_relat_1(esk7_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44])])).
% 0.18/0.36  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.18/0.36  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_48])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 50
% 0.18/0.36  # Proof object clause steps            : 33
% 0.18/0.36  # Proof object formula steps           : 17
% 0.18/0.36  # Proof object conjectures             : 21
% 0.18/0.36  # Proof object clause conjectures      : 18
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 15
% 0.18/0.36  # Proof object initial formulas used   : 8
% 0.18/0.36  # Proof object generating inferences   : 11
% 0.18/0.36  # Proof object simplifying inferences  : 13
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 8
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 20
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 20
% 0.18/0.36  # Processed clauses                    : 68
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 2
% 0.18/0.36  # ...remaining for further processing  : 66
% 0.18/0.36  # Other redundant clauses eliminated   : 4
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 17
% 0.18/0.36  # Generated clauses                    : 63
% 0.18/0.36  # ...of the previous two non-trivial   : 52
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 59
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 4
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 26
% 0.18/0.36  #    Positive orientable unit clauses  : 6
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 0
% 0.18/0.36  #    Non-unit-clauses                  : 20
% 0.18/0.36  # Current number of unprocessed clauses: 19
% 0.18/0.36  # ...number of literals in the above   : 70
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 36
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 110
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 96
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.36  # Unit Clause-clause subsumption calls : 6
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 2
% 0.18/0.36  # BW rewrite match successes           : 2
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 2495
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.030 s
% 0.18/0.36  # System time              : 0.004 s
% 0.18/0.36  # Total time               : 0.034 s
% 0.18/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

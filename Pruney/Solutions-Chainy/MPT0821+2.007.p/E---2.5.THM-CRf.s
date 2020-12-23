%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:19 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 237 expanded)
%              Number of clauses        :   37 ( 111 expanded)
%              Number of leaves         :    9 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 817 expanded)
%              Number of equality atoms :   40 ( 225 expanded)
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

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
        <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t22_relset_1])).

fof(c_0_10,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | r1_tarski(X20,X18)
        | X19 != k1_zfmisc_1(X18) )
      & ( ~ r1_tarski(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k1_zfmisc_1(X18) )
      & ( ~ r2_hidden(esk3_2(X22,X23),X23)
        | ~ r1_tarski(esk3_2(X22,X23),X22)
        | X23 = k1_zfmisc_1(X22) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | r1_tarski(esk3_2(X22,X23),X22)
        | X23 = k1_zfmisc_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_relset_1(X41,X42,X43) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X48,X49] :
      ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))
      & ( r2_hidden(esk10_0,esk8_0)
        | k1_relset_1(esk8_0,esk7_0,esk9_0) != esk8_0 )
      & ( ~ r2_hidden(k4_tarski(esk10_0,X48),esk9_0)
        | k1_relset_1(esk8_0,esk7_0,esk9_0) != esk8_0 )
      & ( ~ r2_hidden(X49,esk8_0)
        | r2_hidden(k4_tarski(X49,esk11_1(X49)),esk9_0)
        | k1_relset_1(esk8_0,esk7_0,esk9_0) = esk8_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | m1_subset_1(k1_relset_1(X38,X39,X40),k1_zfmisc_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X25,X26)
      | v1_xboole_0(X26)
      | r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k1_relset_1(esk8_0,esk7_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(X29,esk4_3(X27,X28,X29)),X27)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X31,X32),X27)
        | r2_hidden(X31,X28)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(esk5_2(X33,X34),X34)
        | ~ r2_hidden(k4_tarski(esk5_2(X33,X34),X36),X33)
        | X34 = k1_relat_1(X33) )
      & ( r2_hidden(esk5_2(X33,X34),X34)
        | r2_hidden(k4_tarski(esk5_2(X33,X34),esk6_2(X33,X34)),X33)
        | X34 = k1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk11_1(X1)),esk9_0)
    | k1_relset_1(esk8_0,esk7_0,esk9_0) = esk8_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_29,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk9_0),k1_zfmisc_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_18])])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk8_0
    | r2_hidden(k4_tarski(X1,esk11_1(X1)),esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_relat_1(esk9_0),k1_zfmisc_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk10_0,X1),esk9_0)
    | k1_relset_1(esk8_0,esk7_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk8_0
    | r1_tarski(esk8_0,X1)
    | r2_hidden(k4_tarski(esk2_2(esk8_0,X1),esk11_1(esk2_2(esk8_0,X1))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk9_0) != esk8_0
    | ~ r2_hidden(k4_tarski(esk10_0,X1),esk9_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk8_0
    | r1_tarski(esk8_0,X1)
    | r2_hidden(esk2_2(esk8_0,X1),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk8_0
    | ~ r1_tarski(esk8_0,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk10_0,esk8_0)
    | k1_relset_1(esk8_0,esk7_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(esk9_0) != esk8_0
    | ~ r2_hidden(esk10_0,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk8_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk10_0,esk8_0)
    | k1_relat_1(esk9_0) != esk8_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk10_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_52])]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t22_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 0.20/0.43  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.43  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.43  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.20/0.43  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.43  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2))), inference(assume_negation,[status(cth)],[t22_relset_1])).
% 0.20/0.43  fof(c_0_10, plain, ![X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X20,X19)|r1_tarski(X20,X18)|X19!=k1_zfmisc_1(X18))&(~r1_tarski(X21,X18)|r2_hidden(X21,X19)|X19!=k1_zfmisc_1(X18)))&((~r2_hidden(esk3_2(X22,X23),X23)|~r1_tarski(esk3_2(X22,X23),X22)|X23=k1_zfmisc_1(X22))&(r2_hidden(esk3_2(X22,X23),X23)|r1_tarski(esk3_2(X22,X23),X22)|X23=k1_zfmisc_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.43  fof(c_0_11, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k1_relset_1(X41,X42,X43)=k1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.43  fof(c_0_12, negated_conjecture, ![X48, X49]:(m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))&(((r2_hidden(esk10_0,esk8_0)|k1_relset_1(esk8_0,esk7_0,esk9_0)!=esk8_0)&(~r2_hidden(k4_tarski(esk10_0,X48),esk9_0)|k1_relset_1(esk8_0,esk7_0,esk9_0)!=esk8_0))&(~r2_hidden(X49,esk8_0)|r2_hidden(k4_tarski(X49,esk11_1(X49)),esk9_0)|k1_relset_1(esk8_0,esk7_0,esk9_0)=esk8_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).
% 0.20/0.43  fof(c_0_13, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  cnf(c_0_14, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  fof(c_0_15, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.43  fof(c_0_16, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|m1_subset_1(k1_relset_1(X38,X39,X40),k1_zfmisc_1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.20/0.43  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_19, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_20, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  fof(c_0_22, plain, ![X25, X26]:(~m1_subset_1(X25,X26)|(v1_xboole_0(X26)|r2_hidden(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.43  cnf(c_0_23, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_24, negated_conjecture, (k1_relset_1(esk8_0,esk7_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.43  cnf(c_0_25, plain, (~r1_tarski(X1,X2)|~v1_xboole_0(k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.43  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.43  fof(c_0_27, plain, ![X27, X28, X29, X31, X32, X33, X34, X36]:(((~r2_hidden(X29,X28)|r2_hidden(k4_tarski(X29,esk4_3(X27,X28,X29)),X27)|X28!=k1_relat_1(X27))&(~r2_hidden(k4_tarski(X31,X32),X27)|r2_hidden(X31,X28)|X28!=k1_relat_1(X27)))&((~r2_hidden(esk5_2(X33,X34),X34)|~r2_hidden(k4_tarski(esk5_2(X33,X34),X36),X33)|X34=k1_relat_1(X33))&(r2_hidden(esk5_2(X33,X34),X34)|r2_hidden(k4_tarski(esk5_2(X33,X34),esk6_2(X33,X34)),X33)|X34=k1_relat_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.43  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(X1,esk11_1(X1)),esk9_0)|k1_relset_1(esk8_0,esk7_0,esk9_0)=esk8_0|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  fof(c_0_29, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.43  cnf(c_0_31, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_32, negated_conjecture, (m1_subset_1(k1_relat_1(esk9_0),k1_zfmisc_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_18])])).
% 0.20/0.43  cnf(c_0_33, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.43  cnf(c_0_34, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (k1_relat_1(esk9_0)=esk8_0|r2_hidden(k4_tarski(X1,esk11_1(X1)),esk9_0)|~r2_hidden(X1,esk8_0)), inference(rw,[status(thm)],[c_0_28, c_0_24])).
% 0.20/0.43  cnf(c_0_36, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_relat_1(esk9_0),k1_zfmisc_1(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.43  cnf(c_0_39, negated_conjecture, (~r2_hidden(k4_tarski(esk10_0,X1),esk9_0)|k1_relset_1(esk8_0,esk7_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_41, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, (k1_relat_1(esk9_0)=esk8_0|r1_tarski(esk8_0,X1)|r2_hidden(k4_tarski(esk2_2(esk8_0,X1),esk11_1(esk2_2(esk8_0,X1))),esk9_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.43  cnf(c_0_43, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk9_0)!=esk8_0|~r2_hidden(k4_tarski(esk10_0,X1),esk9_0)), inference(rw,[status(thm)],[c_0_39, c_0_24])).
% 0.20/0.43  cnf(c_0_46, plain, (r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.43  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk9_0)=esk8_0|r1_tarski(esk8_0,X1)|r2_hidden(esk2_2(esk8_0,X1),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk9_0)=esk8_0|~r1_tarski(esk8_0,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (r2_hidden(esk10_0,esk8_0)|k1_relset_1(esk8_0,esk7_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (k1_relat_1(esk9_0)!=esk8_0|~r2_hidden(esk10_0,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.43  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk9_0)=esk8_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (r2_hidden(esk10_0,esk8_0)|k1_relat_1(esk9_0)!=esk8_0), inference(rw,[status(thm)],[c_0_50, c_0_24])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk10_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_52])])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_52])]), c_0_54]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 56
% 0.20/0.43  # Proof object clause steps            : 37
% 0.20/0.43  # Proof object formula steps           : 19
% 0.20/0.43  # Proof object conjectures             : 21
% 0.20/0.43  # Proof object clause conjectures      : 18
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 16
% 0.20/0.43  # Proof object initial formulas used   : 9
% 0.20/0.43  # Proof object generating inferences   : 11
% 0.20/0.43  # Proof object simplifying inferences  : 18
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 9
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 23
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 23
% 0.20/0.43  # Processed clauses                    : 815
% 0.20/0.43  # ...of these trivial                  : 1
% 0.20/0.43  # ...subsumed                          : 526
% 0.20/0.43  # ...remaining for further processing  : 287
% 0.20/0.43  # Other redundant clauses eliminated   : 6
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 6
% 0.20/0.43  # Backward-rewritten                   : 110
% 0.20/0.43  # Generated clauses                    : 2489
% 0.20/0.43  # ...of the previous two non-trivial   : 2517
% 0.20/0.43  # Contextual simplify-reflections      : 4
% 0.20/0.43  # Paramodulations                      : 2476
% 0.20/0.43  # Factorizations                       : 6
% 0.20/0.43  # Equation resolutions                 : 6
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 142
% 0.20/0.43  #    Positive orientable unit clauses  : 8
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 6
% 0.20/0.43  #    Non-unit-clauses                  : 128
% 0.20/0.43  # Current number of unprocessed clauses: 1744
% 0.20/0.43  # ...number of literals in the above   : 5847
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 139
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 6038
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 4172
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 346
% 0.20/0.43  # Unit Clause-clause subsumption calls : 55
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 3
% 0.20/0.43  # BW rewrite match successes           : 2
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 34309
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.085 s
% 0.20/0.43  # System time              : 0.003 s
% 0.20/0.43  # Total time               : 0.088 s
% 0.20/0.43  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:48:20 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   56 (  99 expanded)
%              Number of clauses        :   35 (  48 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 293 expanded)
%              Number of equality atoms :   41 (  66 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t30_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X22] : r1_tarski(X22,k1_zfmisc_1(k3_tarski(X22))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X11
        | X14 = X12
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X11
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( esk2_3(X16,X17,X18) != X16
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( esk2_3(X16,X17,X18) != X17
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | esk2_3(X16,X17,X18) = X16
        | esk2_3(X16,X17,X18) = X17
        | X18 = k2_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X49] :
      ( ~ v1_relat_1(X49)
      | k3_relat_1(X49) = k2_xboole_0(k1_relat_1(X49),k2_relat_1(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_14,plain,(
    ! [X20,X21] : k3_tarski(k2_tarski(X20,X21)) = k2_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
         => ( r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)
    & ( ~ r2_hidden(esk9_0,k3_relat_1(esk11_0))
      | ~ r2_hidden(esk10_0,k3_relat_1(esk11_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_24,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_27,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | m1_subset_1(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_relat_1(esk11_0),k2_relat_1(esk11_0))) = k3_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

fof(c_0_31,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k2_relat_1(esk11_0),k1_zfmisc_1(k3_relat_1(esk11_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,plain,(
    ! [X38,X39,X40,X42,X43,X44,X45,X47] :
      ( ( ~ r2_hidden(X40,X39)
        | r2_hidden(k4_tarski(esk6_3(X38,X39,X40),X40),X38)
        | X39 != k2_relat_1(X38) )
      & ( ~ r2_hidden(k4_tarski(X43,X42),X38)
        | r2_hidden(X42,X39)
        | X39 != k2_relat_1(X38) )
      & ( ~ r2_hidden(esk7_2(X44,X45),X45)
        | ~ r2_hidden(k4_tarski(X47,esk7_2(X44,X45)),X44)
        | X45 = k2_relat_1(X44) )
      & ( r2_hidden(esk7_2(X44,X45),X45)
        | r2_hidden(k4_tarski(esk8_2(X44,X45),esk7_2(X44,X45)),X44)
        | X45 = k2_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk11_0),k1_zfmisc_1(k3_relat_1(esk11_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_relat_1(esk11_0),k1_zfmisc_1(k3_relat_1(esk11_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

fof(c_0_40,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(X29,esk3_3(X27,X28,X29)),X27)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X31,X32),X27)
        | r2_hidden(X31,X28)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(esk4_2(X33,X34),X34)
        | ~ r2_hidden(k4_tarski(esk4_2(X33,X34),X36),X33)
        | X34 = k1_relat_1(X33) )
      & ( r2_hidden(esk4_2(X33,X34),X34)
        | r2_hidden(k4_tarski(esk4_2(X33,X34),esk5_2(X33,X34)),X33)
        | X34 = k1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk11_0),k3_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk11_0),k1_zfmisc_1(k3_relat_1(esk11_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk11_0))
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk11_0),k3_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k3_relat_1(esk11_0))
    | ~ r2_hidden(esk10_0,k3_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk10_0,k3_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk11_0))
    | ~ r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:44:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.18/0.39  # and selection function SelectCQIArEqFirst.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.028 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.39  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.18/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.18/0.39  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.18/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.18/0.39  fof(t30_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.18/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.18/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.39  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.18/0.39  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.18/0.39  fof(c_0_10, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.39  fof(c_0_11, plain, ![X22]:r1_tarski(X22,k1_zfmisc_1(k3_tarski(X22))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.18/0.39  fof(c_0_12, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(X14=X11|X14=X12)|X13!=k2_tarski(X11,X12))&((X15!=X11|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))))&(((esk2_3(X16,X17,X18)!=X16|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17))&(esk2_3(X16,X17,X18)!=X17|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(esk2_3(X16,X17,X18)=X16|esk2_3(X16,X17,X18)=X17)|X18=k2_tarski(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.18/0.39  fof(c_0_13, plain, ![X49]:(~v1_relat_1(X49)|k3_relat_1(X49)=k2_xboole_0(k1_relat_1(X49),k2_relat_1(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.18/0.39  fof(c_0_14, plain, ![X20, X21]:k3_tarski(k2_tarski(X20,X21))=k2_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.18/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3)))))), inference(assume_negation,[status(cth)],[t30_relat_1])).
% 0.18/0.39  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_17, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.39  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_19, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  fof(c_0_21, negated_conjecture, (v1_relat_1(esk11_0)&(r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)&(~r2_hidden(esk9_0,k3_relat_1(esk11_0))|~r2_hidden(esk10_0,k3_relat_1(esk11_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.18/0.39  cnf(c_0_22, plain, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(X2)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.39  cnf(c_0_23, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 0.18/0.39  cnf(c_0_24, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.39  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  fof(c_0_27, plain, ![X23, X24]:(~r2_hidden(X23,X24)|m1_subset_1(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.18/0.39  cnf(c_0_28, plain, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1))))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.39  cnf(c_0_29, negated_conjecture, (k3_tarski(k2_tarski(k1_relat_1(esk11_0),k2_relat_1(esk11_0)))=k3_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.39  cnf(c_0_30, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 0.18/0.39  fof(c_0_31, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.39  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(k2_relat_1(esk11_0),k1_zfmisc_1(k3_relat_1(esk11_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.39  fof(c_0_34, plain, ![X38, X39, X40, X42, X43, X44, X45, X47]:(((~r2_hidden(X40,X39)|r2_hidden(k4_tarski(esk6_3(X38,X39,X40),X40),X38)|X39!=k2_relat_1(X38))&(~r2_hidden(k4_tarski(X43,X42),X38)|r2_hidden(X42,X39)|X39!=k2_relat_1(X38)))&((~r2_hidden(esk7_2(X44,X45),X45)|~r2_hidden(k4_tarski(X47,esk7_2(X44,X45)),X44)|X45=k2_relat_1(X44))&(r2_hidden(esk7_2(X44,X45),X45)|r2_hidden(k4_tarski(esk8_2(X44,X45),esk7_2(X44,X45)),X44)|X45=k2_relat_1(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.18/0.39  cnf(c_0_35, plain, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 0.18/0.39  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(k2_relat_1(esk11_0),k1_zfmisc_1(k3_relat_1(esk11_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.39  cnf(c_0_38, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(k1_relat_1(esk11_0),k1_zfmisc_1(k3_relat_1(esk11_0)))), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 0.18/0.39  fof(c_0_40, plain, ![X27, X28, X29, X31, X32, X33, X34, X36]:(((~r2_hidden(X29,X28)|r2_hidden(k4_tarski(X29,esk3_3(X27,X28,X29)),X27)|X28!=k1_relat_1(X27))&(~r2_hidden(k4_tarski(X31,X32),X27)|r2_hidden(X31,X28)|X28!=k1_relat_1(X27)))&((~r2_hidden(esk4_2(X33,X34),X34)|~r2_hidden(k4_tarski(esk4_2(X33,X34),X36),X33)|X34=k1_relat_1(X33))&(r2_hidden(esk4_2(X33,X34),X34)|r2_hidden(k4_tarski(esk4_2(X33,X34),esk5_2(X33,X34)),X33)|X34=k1_relat_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.18/0.39  cnf(c_0_41, negated_conjecture, (r1_tarski(k2_relat_1(esk11_0),k3_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.39  cnf(c_0_42, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_38])).
% 0.18/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_44, negated_conjecture, (m1_subset_1(k1_relat_1(esk11_0),k1_zfmisc_1(k3_relat_1(esk11_0)))), inference(spm,[status(thm)],[c_0_32, c_0_39])).
% 0.18/0.39  cnf(c_0_45, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk11_0))|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_16, c_0_41])).
% 0.18/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(esk10_0,k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.39  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_relat_1(esk11_0),k3_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_36, c_0_44])).
% 0.18/0.39  cnf(c_0_49, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_50, negated_conjecture, (~r2_hidden(esk9_0,k3_relat_1(esk11_0))|~r2_hidden(esk10_0,k3_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(esk10_0,k3_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.39  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk11_0))|~r2_hidden(X1,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_16, c_0_48])).
% 0.18/0.39  cnf(c_0_53, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_49, c_0_43])).
% 0.18/0.39  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk9_0,k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.18/0.39  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 56
% 0.18/0.39  # Proof object clause steps            : 35
% 0.18/0.39  # Proof object formula steps           : 21
% 0.18/0.39  # Proof object conjectures             : 20
% 0.18/0.39  # Proof object clause conjectures      : 17
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 13
% 0.18/0.39  # Proof object initial formulas used   : 10
% 0.18/0.39  # Proof object generating inferences   : 16
% 0.18/0.39  # Proof object simplifying inferences  : 10
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 10
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 26
% 0.18/0.39  # Removed in clause preprocessing      : 1
% 0.18/0.39  # Initial clauses in saturation        : 25
% 0.18/0.39  # Processed clauses                    : 159
% 0.18/0.39  # ...of these trivial                  : 0
% 0.18/0.39  # ...subsumed                          : 3
% 0.18/0.39  # ...remaining for further processing  : 156
% 0.18/0.39  # Other redundant clauses eliminated   : 17
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 11
% 0.18/0.39  # Backward-rewritten                   : 1
% 0.18/0.39  # Generated clauses                    : 813
% 0.18/0.39  # ...of the previous two non-trivial   : 788
% 0.18/0.39  # Contextual simplify-reflections      : 0
% 0.18/0.39  # Paramodulations                      : 796
% 0.18/0.39  # Factorizations                       : 2
% 0.18/0.39  # Equation resolutions                 : 17
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 112
% 0.18/0.39  #    Positive orientable unit clauses  : 52
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 1
% 0.18/0.39  #    Non-unit-clauses                  : 59
% 0.18/0.39  # Current number of unprocessed clauses: 677
% 0.18/0.39  # ...number of literals in the above   : 2597
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 38
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 1359
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 372
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 14
% 0.18/0.39  # Unit Clause-clause subsumption calls : 209
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 28
% 0.18/0.39  # BW rewrite match successes           : 1
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 17828
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.044 s
% 0.18/0.39  # System time              : 0.008 s
% 0.18/0.39  # Total time               : 0.052 s
% 0.18/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

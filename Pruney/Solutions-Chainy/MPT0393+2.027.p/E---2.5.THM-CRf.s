%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 338 expanded)
%              Number of clauses        :   40 ( 148 expanded)
%              Number of leaves         :   12 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 701 expanded)
%              Number of equality atoms :   72 ( 416 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X16
        | X19 = X17
        | X18 != k2_tarski(X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k2_tarski(X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k2_tarski(X16,X17) )
      & ( esk2_3(X21,X22,X23) != X21
        | ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k2_tarski(X21,X22) )
      & ( esk2_3(X21,X22,X23) != X22
        | ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k2_tarski(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X23)
        | esk2_3(X21,X22,X23) = X21
        | esk2_3(X21,X22,X23) = X22
        | X23 = k2_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_14,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X47,X48,X49] :
      ( ~ r2_hidden(X47,X48)
      | ~ r1_tarski(X47,X49)
      | r1_tarski(k1_setfam_1(X48),X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

fof(c_0_22,plain,(
    ! [X36,X37] :
      ( ~ r1_tarski(k1_tarski(X36),k1_tarski(X37))
      | X36 = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

fof(c_0_23,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X39,X40] :
      ( ( ~ m1_subset_1(X39,k1_zfmisc_1(X40))
        | r1_tarski(X39,X40) )
      & ( ~ r1_tarski(X39,X40)
        | m1_subset_1(X39,k1_zfmisc_1(X40)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_25,plain,(
    ! [X38] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X38)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

fof(c_0_29,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk4_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X44,X45] :
      ( ( r2_hidden(esk3_2(X44,X45),X44)
        | X44 = k1_xboole_0
        | r1_tarski(X45,k1_setfam_1(X44)) )
      & ( ~ r1_tarski(X45,esk3_2(X44,X45))
        | X44 = k1_xboole_0
        | r1_tarski(X45,k1_setfam_1(X44)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk4_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31]),c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_39,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_31]),c_0_19]),c_0_20])).

cnf(c_0_45,plain,
    ( X1 = X2
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | r2_hidden(esk3_2(k2_enumset1(X1,X1,X1,X1),X3),k2_enumset1(X1,X1,X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

fof(c_0_46,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,X34)
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( X33 != X35
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( ~ r2_hidden(X33,X34)
        | X33 = X35
        | r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_47,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_19]),c_0_20])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))
    | r2_hidden(esk3_2(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_50,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_2(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk4_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_44])).

cnf(c_0_53,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_31]),c_0_19]),c_0_20])).

cnf(c_0_54,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk3_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( esk3_2(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( X1 = X2
    | r2_hidden(X1,k4_xboole_0(k2_enumset1(X3,X3,X3,X1),k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_36])).

cnf(c_0_58,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_31]),c_0_19]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | r1_tarski(esk4_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_27])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k4_xboole_0(k2_enumset1(X2,X2,X2,X1),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) != X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_57])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 = X1
    | r1_tarski(esk4_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_59]),c_0_40])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk4_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_61]),c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_63]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:53:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.43  # and selection function SelectNegativeLiterals.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.028 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.43  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 0.19/0.43  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.19/0.43  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.19/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.43  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.43  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.19/0.43  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.19/0.43  fof(c_0_12, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  fof(c_0_13, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(X19=X16|X19=X17)|X18!=k2_tarski(X16,X17))&((X20!=X16|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))&(X20!=X17|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))))&(((esk2_3(X21,X22,X23)!=X21|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22))&(esk2_3(X21,X22,X23)!=X22|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22)))&(r2_hidden(esk2_3(X21,X22,X23),X23)|(esk2_3(X21,X22,X23)=X21|esk2_3(X21,X22,X23)=X22)|X23=k2_tarski(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.43  fof(c_0_14, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.43  fof(c_0_15, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.43  fof(c_0_16, plain, ![X47, X48, X49]:(~r2_hidden(X47,X48)|~r1_tarski(X47,X49)|r1_tarski(k1_setfam_1(X48),X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 0.19/0.43  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  fof(c_0_21, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.19/0.43  fof(c_0_22, plain, ![X36, X37]:(~r1_tarski(k1_tarski(X36),k1_tarski(X37))|X36=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.19/0.43  fof(c_0_23, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.43  fof(c_0_24, plain, ![X39, X40]:((~m1_subset_1(X39,k1_zfmisc_1(X40))|r1_tarski(X39,X40))&(~r1_tarski(X39,X40)|m1_subset_1(X39,k1_zfmisc_1(X40)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.43  fof(c_0_25, plain, ![X38]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X38)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.43  cnf(c_0_26, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.43  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.43  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.43  fof(c_0_29, negated_conjecture, k1_setfam_1(k1_tarski(esk4_0))!=esk4_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.19/0.43  cnf(c_0_30, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.43  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.43  fof(c_0_32, plain, ![X44, X45]:((r2_hidden(esk3_2(X44,X45),X44)|(X44=k1_xboole_0|r1_tarski(X45,k1_setfam_1(X44))))&(~r1_tarski(X45,esk3_2(X44,X45))|(X44=k1_xboole_0|r1_tarski(X45,k1_setfam_1(X44))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.19/0.43  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.43  cnf(c_0_34, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.43  cnf(c_0_35, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.43  cnf(c_0_36, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 0.19/0.43  cnf(c_0_37, negated_conjecture, (k1_setfam_1(k1_tarski(esk4_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.43  cnf(c_0_38, plain, (X1=X2|~r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_31]), c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.19/0.43  cnf(c_0_39, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.43  cnf(c_0_41, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.43  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.43  cnf(c_0_43, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.43  cnf(c_0_44, negated_conjecture, (k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_31]), c_0_19]), c_0_20])).
% 0.19/0.43  cnf(c_0_45, plain, (X1=X2|r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))|r2_hidden(esk3_2(k2_enumset1(X1,X1,X1,X1),X3),k2_enumset1(X1,X1,X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.19/0.43  fof(c_0_46, plain, ![X33, X34, X35]:(((r2_hidden(X33,X34)|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))&(X33!=X35|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35)))))&(~r2_hidden(X33,X34)|X33=X35|r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.19/0.43  cnf(c_0_47, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_19]), c_0_20])).
% 0.19/0.43  cnf(c_0_48, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|~r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.43  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))|r2_hidden(esk3_2(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45])])).
% 0.19/0.43  cnf(c_0_50, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.43  cnf(c_0_51, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_47])).
% 0.19/0.43  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_2(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk4_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_44])).
% 0.19/0.43  cnf(c_0_53, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_31]), c_0_19]), c_0_20])).
% 0.19/0.43  cnf(c_0_54, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.43  cnf(c_0_55, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk3_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.43  cnf(c_0_56, negated_conjecture, (esk3_2(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.43  cnf(c_0_57, plain, (X1=X2|r2_hidden(X1,k4_xboole_0(k2_enumset1(X3,X3,X3,X1),k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_36])).
% 0.19/0.43  cnf(c_0_58, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_31]), c_0_19]), c_0_20])).
% 0.19/0.43  cnf(c_0_59, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|r1_tarski(esk4_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_27])])).
% 0.19/0.43  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k4_xboole_0(k2_enumset1(X2,X2,X2,X1),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))|k1_setfam_1(k2_enumset1(X1,X1,X1,X1))!=X1), inference(spm,[status(thm)],[c_0_44, c_0_57])).
% 0.19/0.43  cnf(c_0_61, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_58])).
% 0.19/0.43  cnf(c_0_62, negated_conjecture, (esk4_0=X1|r1_tarski(esk4_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_59]), c_0_40])])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (r1_tarski(esk4_0,k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_61]), c_0_62])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_63]), c_0_44]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 65
% 0.19/0.43  # Proof object clause steps            : 40
% 0.19/0.43  # Proof object formula steps           : 25
% 0.19/0.43  # Proof object conjectures             : 13
% 0.19/0.43  # Proof object clause conjectures      : 10
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 16
% 0.19/0.43  # Proof object initial formulas used   : 12
% 0.19/0.43  # Proof object generating inferences   : 14
% 0.19/0.43  # Proof object simplifying inferences  : 35
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 15
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 32
% 0.19/0.43  # Removed in clause preprocessing      : 3
% 0.19/0.43  # Initial clauses in saturation        : 29
% 0.19/0.43  # Processed clauses                    : 307
% 0.19/0.43  # ...of these trivial                  : 4
% 0.19/0.43  # ...subsumed                          : 126
% 0.19/0.43  # ...remaining for further processing  : 177
% 0.19/0.43  # Other redundant clauses eliminated   : 188
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 3
% 0.19/0.43  # Backward-rewritten                   : 7
% 0.19/0.43  # Generated clauses                    : 5303
% 0.19/0.43  # ...of the previous two non-trivial   : 4957
% 0.19/0.43  # Contextual simplify-reflections      : 1
% 0.19/0.43  # Paramodulations                      : 5113
% 0.19/0.43  # Factorizations                       : 4
% 0.19/0.43  # Equation resolutions                 : 188
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 131
% 0.19/0.43  #    Positive orientable unit clauses  : 26
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 6
% 0.19/0.43  #    Non-unit-clauses                  : 99
% 0.19/0.43  # Current number of unprocessed clauses: 4696
% 0.19/0.43  # ...number of literals in the above   : 17115
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 40
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 1319
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 970
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 125
% 0.19/0.43  # Unit Clause-clause subsumption calls : 109
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 21
% 0.19/0.43  # BW rewrite match successes           : 5
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 87631
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.098 s
% 0.19/0.44  # System time              : 0.006 s
% 0.19/0.44  # Total time               : 0.104 s
% 0.19/0.44  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

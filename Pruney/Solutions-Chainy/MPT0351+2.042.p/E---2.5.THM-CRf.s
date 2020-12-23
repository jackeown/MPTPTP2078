%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:31 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 183 expanded)
%              Number of clauses        :   30 (  82 expanded)
%              Number of leaves         :   11 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 321 expanded)
%              Number of equality atoms :   43 ( 151 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k2_subset_1(X1)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t28_subset_1])).

fof(c_0_12,plain,(
    ! [X107,X108,X109] :
      ( ~ m1_subset_1(X108,k1_zfmisc_1(X107))
      | ~ m1_subset_1(X109,k1_zfmisc_1(X107))
      | k4_subset_1(X107,X108,X109) = k2_xboole_0(X108,X109) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_13,plain,(
    ! [X87,X88] : k2_xboole_0(X87,X88) = k5_xboole_0(X87,k4_xboole_0(X88,X87)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_14,plain,(
    ! [X89,X90,X91] :
      ( ~ m1_subset_1(X90,k1_zfmisc_1(X89))
      | ~ m1_subset_1(X91,k1_zfmisc_1(X89))
      | k4_subset_1(X89,X90,X91) = k4_subset_1(X89,X91,X90) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

fof(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & k4_subset_1(esk5_0,esk6_0,k2_subset_1(esk5_0)) != k2_subset_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X95] : m1_subset_1(k2_subset_1(X95),k1_zfmisc_1(X95)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_17,plain,(
    ! [X92] : k2_subset_1(X92) = X92 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_18,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_21,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X84] : k5_xboole_0(X84,k1_xboole_0) = X84 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_26,plain,(
    ! [X41] :
      ( X41 = k1_xboole_0
      | r2_hidden(esk4_1(X41),X41) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_27,plain,
    ( k4_subset_1(X2,X1,X3) = k5_xboole_0(X1,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,X1) = k4_subset_1(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k2_subset_1(esk5_0)) != k2_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_32,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( r2_hidden(X32,X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X33,X29)
        | r2_hidden(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk3_3(X34,X35,X36),X36)
        | ~ r2_hidden(esk3_3(X34,X35,X36),X34)
        | r2_hidden(esk3_3(X34,X35,X36),X35)
        | X36 = k4_xboole_0(X34,X35) )
      & ( r2_hidden(esk3_3(X34,X35,X36),X34)
        | r2_hidden(esk3_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) )
      & ( ~ r2_hidden(esk3_3(X34,X35,X36),X35)
        | r2_hidden(esk3_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k5_xboole_0(esk6_0,k4_xboole_0(X1,esk6_0)) = k4_subset_1(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,esk5_0) = k4_subset_1(esk5_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,esk5_0) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_24]),c_0_24])).

fof(c_0_39,plain,(
    ! [X104,X105,X106] :
      ( ~ m1_subset_1(X105,k1_zfmisc_1(X104))
      | ~ r2_hidden(X106,X105)
      | r2_hidden(X106,X104) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = X1
    | r2_hidden(esk4_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk5_0)) = k4_subset_1(esk5_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_36]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k4_subset_1(esk5_0,esk5_0,esk6_0) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk5_0)),k4_xboole_0(esk6_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:01:31 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.85/1.01  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.85/1.01  # and selection function SelectNegativeLiterals.
% 0.85/1.01  #
% 0.85/1.01  # Preprocessing time       : 0.030 s
% 0.85/1.01  # Presaturation interreduction done
% 0.85/1.01  
% 0.85/1.01  # Proof found!
% 0.85/1.01  # SZS status Theorem
% 0.85/1.01  # SZS output start CNFRefutation
% 0.85/1.01  fof(t28_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 0.85/1.01  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.85/1.01  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.85/1.01  fof(commutativity_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k4_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 0.85/1.01  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.85/1.01  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.85/1.01  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.85/1.01  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.85/1.01  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.85/1.01  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.85/1.01  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.85/1.01  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k2_subset_1(X1))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t28_subset_1])).
% 0.85/1.01  fof(c_0_12, plain, ![X107, X108, X109]:(~m1_subset_1(X108,k1_zfmisc_1(X107))|~m1_subset_1(X109,k1_zfmisc_1(X107))|k4_subset_1(X107,X108,X109)=k2_xboole_0(X108,X109)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.85/1.01  fof(c_0_13, plain, ![X87, X88]:k2_xboole_0(X87,X88)=k5_xboole_0(X87,k4_xboole_0(X88,X87)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.85/1.01  fof(c_0_14, plain, ![X89, X90, X91]:(~m1_subset_1(X90,k1_zfmisc_1(X89))|~m1_subset_1(X91,k1_zfmisc_1(X89))|k4_subset_1(X89,X90,X91)=k4_subset_1(X89,X91,X90)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).
% 0.85/1.01  fof(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&k4_subset_1(esk5_0,esk6_0,k2_subset_1(esk5_0))!=k2_subset_1(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.85/1.01  fof(c_0_16, plain, ![X95]:m1_subset_1(k2_subset_1(X95),k1_zfmisc_1(X95)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.85/1.01  fof(c_0_17, plain, ![X92]:k2_subset_1(X92)=X92, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.85/1.01  cnf(c_0_18, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.85/1.01  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.85/1.01  fof(c_0_20, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.85/1.01  cnf(c_0_21, plain, (k4_subset_1(X2,X1,X3)=k4_subset_1(X2,X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.85/1.01  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.85/1.01  cnf(c_0_23, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.85/1.01  cnf(c_0_24, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.85/1.01  fof(c_0_25, plain, ![X84]:k5_xboole_0(X84,k1_xboole_0)=X84, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.85/1.01  fof(c_0_26, plain, ![X41]:(X41=k1_xboole_0|r2_hidden(esk4_1(X41),X41)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.85/1.01  cnf(c_0_27, plain, (k4_subset_1(X2,X1,X3)=k5_xboole_0(X1,k4_xboole_0(X3,X1))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.85/1.01  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.85/1.01  cnf(c_0_29, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,X1)=k4_subset_1(esk5_0,X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.85/1.01  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.85/1.01  cnf(c_0_31, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k2_subset_1(esk5_0))!=k2_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.85/1.01  fof(c_0_32, plain, ![X29, X30, X31, X32, X33, X34, X35, X36]:((((r2_hidden(X32,X29)|~r2_hidden(X32,X31)|X31!=k4_xboole_0(X29,X30))&(~r2_hidden(X32,X30)|~r2_hidden(X32,X31)|X31!=k4_xboole_0(X29,X30)))&(~r2_hidden(X33,X29)|r2_hidden(X33,X30)|r2_hidden(X33,X31)|X31!=k4_xboole_0(X29,X30)))&((~r2_hidden(esk3_3(X34,X35,X36),X36)|(~r2_hidden(esk3_3(X34,X35,X36),X34)|r2_hidden(esk3_3(X34,X35,X36),X35))|X36=k4_xboole_0(X34,X35))&((r2_hidden(esk3_3(X34,X35,X36),X34)|r2_hidden(esk3_3(X34,X35,X36),X36)|X36=k4_xboole_0(X34,X35))&(~r2_hidden(esk3_3(X34,X35,X36),X35)|r2_hidden(esk3_3(X34,X35,X36),X36)|X36=k4_xboole_0(X34,X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.85/1.01  cnf(c_0_33, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.85/1.01  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.85/1.01  cnf(c_0_35, negated_conjecture, (k5_xboole_0(esk6_0,k4_xboole_0(X1,esk6_0))=k4_subset_1(esk5_0,esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.85/1.01  cnf(c_0_36, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_19])).
% 0.85/1.01  cnf(c_0_37, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,esk5_0)=k4_subset_1(esk5_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.85/1.01  cnf(c_0_38, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,esk5_0)!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_24]), c_0_24])).
% 0.85/1.01  fof(c_0_39, plain, ![X104, X105, X106]:(~m1_subset_1(X105,k1_zfmisc_1(X104))|(~r2_hidden(X106,X105)|r2_hidden(X106,X104))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.85/1.01  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.85/1.01  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=X1|r2_hidden(esk4_1(X2),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.85/1.01  cnf(c_0_42, negated_conjecture, (k5_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk5_0))=k4_subset_1(esk5_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_36]), c_0_37])).
% 0.85/1.01  cnf(c_0_43, negated_conjecture, (k4_subset_1(esk5_0,esk5_0,esk6_0)!=esk5_0), inference(rw,[status(thm)],[c_0_38, c_0_37])).
% 0.85/1.01  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.85/1.01  cnf(c_0_45, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.85/1.01  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_40])).
% 0.85/1.01  cnf(c_0_47, negated_conjecture, (r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk5_0)),k4_xboole_0(esk6_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.85/1.01  cnf(c_0_48, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_44])).
% 0.85/1.01  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 0.85/1.01  cnf(c_0_50, negated_conjecture, (r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.85/1.01  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.85/1.01  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), ['proof']).
% 0.85/1.01  # SZS output end CNFRefutation
% 0.85/1.01  # Proof object total steps             : 53
% 0.85/1.01  # Proof object clause steps            : 30
% 0.85/1.01  # Proof object formula steps           : 23
% 0.85/1.01  # Proof object conjectures             : 16
% 0.85/1.01  # Proof object clause conjectures      : 13
% 0.85/1.01  # Proof object formula conjectures     : 3
% 0.85/1.01  # Proof object initial clauses used    : 13
% 0.85/1.01  # Proof object initial formulas used   : 11
% 0.85/1.01  # Proof object generating inferences   : 10
% 0.85/1.01  # Proof object simplifying inferences  : 13
% 0.85/1.01  # Training examples: 0 positive, 0 negative
% 0.85/1.01  # Parsed axioms                        : 43
% 0.85/1.01  # Removed by relevancy pruning/SinE    : 0
% 0.85/1.01  # Initial clauses                      : 60
% 0.85/1.01  # Removed in clause preprocessing      : 3
% 0.85/1.01  # Initial clauses in saturation        : 57
% 0.85/1.01  # Processed clauses                    : 2080
% 0.85/1.01  # ...of these trivial                  : 115
% 0.85/1.01  # ...subsumed                          : 999
% 0.85/1.01  # ...remaining for further processing  : 966
% 0.85/1.01  # Other redundant clauses eliminated   : 74
% 0.85/1.01  # Clauses deleted for lack of memory   : 0
% 0.85/1.01  # Backward-subsumed                    : 2
% 0.85/1.01  # Backward-rewritten                   : 549
% 0.85/1.01  # Generated clauses                    : 109015
% 0.85/1.01  # ...of the previous two non-trivial   : 54690
% 0.85/1.01  # Contextual simplify-reflections      : 3
% 0.85/1.01  # Paramodulations                      : 108941
% 0.85/1.01  # Factorizations                       : 0
% 0.85/1.01  # Equation resolutions                 : 74
% 0.85/1.01  # Propositional unsat checks           : 0
% 0.85/1.01  #    Propositional check models        : 0
% 0.85/1.01  #    Propositional check unsatisfiable : 0
% 0.85/1.01  #    Propositional clauses             : 0
% 0.85/1.01  #    Propositional clauses after purity: 0
% 0.85/1.01  #    Propositional unsat core size     : 0
% 0.85/1.01  #    Propositional preprocessing time  : 0.000
% 0.85/1.01  #    Propositional encoding time       : 0.000
% 0.85/1.01  #    Propositional solver time         : 0.000
% 0.85/1.01  #    Success case prop preproc time    : 0.000
% 0.85/1.01  #    Success case prop encoding time   : 0.000
% 0.85/1.01  #    Success case prop solver time     : 0.000
% 0.85/1.01  # Current number of processed clauses  : 351
% 0.85/1.01  #    Positive orientable unit clauses  : 195
% 0.85/1.01  #    Positive unorientable unit clauses: 3
% 0.85/1.01  #    Negative unit clauses             : 15
% 0.85/1.01  #    Non-unit-clauses                  : 138
% 0.85/1.01  # Current number of unprocessed clauses: 51876
% 0.85/1.01  # ...number of literals in the above   : 122561
% 0.85/1.01  # Current number of archived formulas  : 0
% 0.85/1.01  # Current number of archived clauses   : 609
% 0.85/1.01  # Clause-clause subsumption calls (NU) : 3973
% 0.85/1.01  # Rec. Clause-clause subsumption calls : 3538
% 0.85/1.01  # Non-unit clause-clause subsumptions  : 416
% 0.85/1.01  # Unit Clause-clause subsumption calls : 352
% 0.85/1.01  # Rewrite failures with RHS unbound    : 0
% 0.85/1.01  # BW rewrite match attempts            : 51124
% 0.85/1.01  # BW rewrite match successes           : 113
% 0.85/1.01  # Condensation attempts                : 0
% 0.85/1.01  # Condensation successes               : 0
% 0.85/1.01  # Termbank termtop insertions          : 2020725
% 0.85/1.01  
% 0.85/1.01  # -------------------------------------------------
% 0.85/1.01  # User time                : 0.662 s
% 0.85/1.01  # System time              : 0.029 s
% 0.85/1.01  # Total time               : 0.691 s
% 0.85/1.01  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------

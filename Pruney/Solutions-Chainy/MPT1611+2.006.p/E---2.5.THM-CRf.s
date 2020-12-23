%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:52 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 149 expanded)
%              Number of clauses        :   23 (  75 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 328 expanded)
%              Number of equality atoms :   52 ( 171 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t19_yellow_1,conjecture,(
    ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t203_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => k11_relat_1(k2_zfmisc_1(X2,X3),X1) = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t203_relat_1)).

fof(c_0_10,plain,(
    ! [X38,X39,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X40,X39)
        | r1_tarski(X40,X38)
        | X39 != k1_zfmisc_1(X38) )
      & ( ~ r1_tarski(X41,X38)
        | r2_hidden(X41,X39)
        | X39 != k1_zfmisc_1(X38) )
      & ( ~ r2_hidden(esk2_2(X42,X43),X43)
        | ~ r1_tarski(esk2_2(X42,X43),X42)
        | X43 = k1_zfmisc_1(X42) )
      & ( r2_hidden(esk2_2(X42,X43),X43)
        | r1_tarski(esk2_2(X42,X43),X42)
        | X43 = k1_zfmisc_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t19_yellow_1])).

fof(c_0_13,plain,(
    ! [X72] : k3_yellow_1(X72) = k2_yellow_1(k9_setfam_1(X72)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_14,plain,(
    ! [X70] : k9_setfam_1(X70) = k1_zfmisc_1(X70) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,(
    k4_yellow_0(k3_yellow_1(esk9_0)) != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_18,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X71] :
      ( v1_xboole_0(X71)
      | ~ r2_hidden(k3_tarski(X71),X71)
      | k4_yellow_0(k2_yellow_1(X71)) = k3_tarski(X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_21,plain,(
    ! [X55] : k3_tarski(k1_zfmisc_1(X55)) = X55 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k4_yellow_0(k3_yellow_1(esk9_0)) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X14] :
      ( ~ v1_xboole_0(X14)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_30,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(esk9_0))) != esk9_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1))) = X1
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_34,plain,(
    ! [X53,X54] :
      ( ( k2_zfmisc_1(X53,X54) != k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 )
      & ( X53 != k1_xboole_0
        | k2_zfmisc_1(X53,X54) = k1_xboole_0 )
      & ( X54 != k1_xboole_0
        | k2_zfmisc_1(X53,X54) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_35,plain,(
    ! [X56,X57,X58] :
      ( ~ r2_hidden(X56,X57)
      | k11_relat_1(k2_zfmisc_1(X57,X58),X56) = X58 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t203_relat_1])])).

cnf(c_0_36,negated_conjecture,
    ( k1_zfmisc_1(esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( k11_relat_1(k2_zfmisc_1(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_36])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(k1_xboole_0)) != esk9_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k11_relat_1(k1_xboole_0,esk9_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:50:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.38  # and selection function SelectNegativeLiterals.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.029 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(t19_yellow_1, conjecture, ![X1]:k4_yellow_0(k3_yellow_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 0.12/0.38  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.12/0.38  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.12/0.38  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.12/0.38  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.12/0.38  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 0.12/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.38  fof(t203_relat_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>k11_relat_1(k2_zfmisc_1(X2,X3),X1)=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t203_relat_1)).
% 0.12/0.38  fof(c_0_10, plain, ![X38, X39, X40, X41, X42, X43]:(((~r2_hidden(X40,X39)|r1_tarski(X40,X38)|X39!=k1_zfmisc_1(X38))&(~r1_tarski(X41,X38)|r2_hidden(X41,X39)|X39!=k1_zfmisc_1(X38)))&((~r2_hidden(esk2_2(X42,X43),X43)|~r1_tarski(esk2_2(X42,X43),X42)|X43=k1_zfmisc_1(X42))&(r2_hidden(esk2_2(X42,X43),X43)|r1_tarski(esk2_2(X42,X43),X42)|X43=k1_zfmisc_1(X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.12/0.38  fof(c_0_11, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:k4_yellow_0(k3_yellow_1(X1))=X1), inference(assume_negation,[status(cth)],[t19_yellow_1])).
% 0.12/0.38  fof(c_0_13, plain, ![X72]:k3_yellow_1(X72)=k2_yellow_1(k9_setfam_1(X72)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.12/0.38  fof(c_0_14, plain, ![X70]:k9_setfam_1(X70)=k1_zfmisc_1(X70), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.12/0.38  cnf(c_0_15, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_17, negated_conjecture, k4_yellow_0(k3_yellow_1(esk9_0))!=esk9_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.38  cnf(c_0_18, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_19, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  fof(c_0_20, plain, ![X71]:(v1_xboole_0(X71)|(~r2_hidden(k3_tarski(X71),X71)|k4_yellow_0(k2_yellow_1(X71))=k3_tarski(X71))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.12/0.38  fof(c_0_21, plain, ![X55]:k3_tarski(k1_zfmisc_1(X55))=X55, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.12/0.38  cnf(c_0_22, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (k4_yellow_0(k3_yellow_1(esk9_0))!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_25, plain, (k3_yellow_1(X1)=k2_yellow_1(k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.38  cnf(c_0_26, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_27, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_28, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.38  fof(c_0_29, plain, ![X14]:(~v1_xboole_0(X14)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(esk9_0)))!=esk9_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.38  cnf(c_0_31, plain, (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1)))=X1|v1_xboole_0(k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.12/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.38  fof(c_0_34, plain, ![X53, X54]:((k2_zfmisc_1(X53,X54)!=k1_xboole_0|(X53=k1_xboole_0|X54=k1_xboole_0))&((X53!=k1_xboole_0|k2_zfmisc_1(X53,X54)=k1_xboole_0)&(X54!=k1_xboole_0|k2_zfmisc_1(X53,X54)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.38  fof(c_0_35, plain, ![X56, X57, X58]:(~r2_hidden(X56,X57)|k11_relat_1(k2_zfmisc_1(X57,X58),X56)=X58), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t203_relat_1])])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (k1_zfmisc_1(esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.38  cnf(c_0_37, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.38  cnf(c_0_38, plain, (k11_relat_1(k2_zfmisc_1(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_36])).
% 0.12/0.38  cnf(c_0_40, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_37])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (k4_yellow_0(k2_yellow_1(k1_xboole_0))!=esk9_0), inference(rw,[status(thm)],[c_0_30, c_0_36])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (k11_relat_1(k1_xboole_0,esk9_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 44
% 0.12/0.38  # Proof object clause steps            : 23
% 0.12/0.38  # Proof object formula steps           : 21
% 0.12/0.38  # Proof object conjectures             : 11
% 0.12/0.38  # Proof object clause conjectures      : 8
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 10
% 0.12/0.38  # Proof object initial formulas used   : 10
% 0.12/0.38  # Proof object generating inferences   : 6
% 0.12/0.38  # Proof object simplifying inferences  : 11
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 18
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 62
% 0.12/0.38  # Removed in clause preprocessing      : 2
% 0.12/0.38  # Initial clauses in saturation        : 60
% 0.12/0.38  # Processed clauses                    : 180
% 0.12/0.38  # ...of these trivial                  : 3
% 0.12/0.38  # ...subsumed                          : 8
% 0.12/0.38  # ...remaining for further processing  : 169
% 0.12/0.38  # Other redundant clauses eliminated   : 32
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 49
% 0.12/0.38  # Generated clauses                    : 924
% 0.12/0.38  # ...of the previous two non-trivial   : 817
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 901
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 32
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
% 0.12/0.38  # Current number of processed clauses  : 40
% 0.12/0.38  #    Positive orientable unit clauses  : 25
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 14
% 0.12/0.38  # Current number of unprocessed clauses: 748
% 0.12/0.38  # ...number of literals in the above   : 1899
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 110
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 347
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 294
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.12/0.38  # Unit Clause-clause subsumption calls : 21
% 0.12/0.38  # Rewrite failures with RHS unbound    : 4
% 0.12/0.38  # BW rewrite match attempts            : 118
% 0.12/0.38  # BW rewrite match successes           : 64
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 11417
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.044 s
% 0.12/0.38  # System time              : 0.002 s
% 0.12/0.38  # Total time               : 0.046 s
% 0.12/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:49:28 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 258 expanded)
%              Number of clauses        :   21 ( 101 expanded)
%              Number of leaves         :   14 (  78 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 320 expanded)
%              Number of equality atoms :   59 ( 267 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t81_relat_1,conjecture,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(c_0_14,plain,(
    ! [X51,X52] : k1_setfam_1(k2_tarski(X51,X52)) = k3_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X49,X50] :
      ( ( k4_xboole_0(X49,k1_tarski(X50)) != X49
        | ~ r2_hidden(X50,X49) )
      & ( r2_hidden(X50,X49)
        | k4_xboole_0(X49,k1_tarski(X50)) = X49 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X12] : k4_xboole_0(k1_xboole_0,X12) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_29,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t81_relat_1])).

fof(c_0_30,plain,(
    ! [X53,X54,X55,X56,X57,X58] :
      ( ( r2_hidden(X55,X53)
        | ~ r2_hidden(k4_tarski(X55,X56),X54)
        | X54 != k6_relat_1(X53)
        | ~ v1_relat_1(X54) )
      & ( X55 = X56
        | ~ r2_hidden(k4_tarski(X55,X56),X54)
        | X54 != k6_relat_1(X53)
        | ~ v1_relat_1(X54) )
      & ( ~ r2_hidden(X57,X53)
        | X57 != X58
        | r2_hidden(k4_tarski(X57,X58),X54)
        | X54 != k6_relat_1(X53)
        | ~ v1_relat_1(X54) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X53,X54),esk6_2(X53,X54)),X54)
        | ~ r2_hidden(esk5_2(X53,X54),X53)
        | esk5_2(X53,X54) != esk6_2(X53,X54)
        | X54 = k6_relat_1(X53)
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(esk5_2(X53,X54),X53)
        | r2_hidden(k4_tarski(esk5_2(X53,X54),esk6_2(X53,X54)),X54)
        | X54 = k6_relat_1(X53)
        | ~ v1_relat_1(X54) )
      & ( esk5_2(X53,X54) = esk6_2(X53,X54)
        | r2_hidden(k4_tarski(esk5_2(X53,X54),esk6_2(X53,X54)),X54)
        | X54 = k6_relat_1(X53)
        | ~ v1_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_31,plain,(
    ! [X61,X62,X65,X67,X68] :
      ( ( ~ v1_relat_1(X61)
        | ~ r2_hidden(X62,X61)
        | X62 = k4_tarski(esk7_2(X61,X62),esk8_2(X61,X62)) )
      & ( r2_hidden(esk9_1(X65),X65)
        | v1_relat_1(X65) )
      & ( esk9_1(X65) != k4_tarski(X67,X68)
        | v1_relat_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r2_hidden(esk9_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_18]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( X1 = k6_relat_1(X2)
    | r2_hidden(k4_tarski(esk5_2(X2,X1),esk6_2(X2,X1)),X1)
    | r2_hidden(esk5_2(X2,X1),X2)
    | r2_hidden(esk9_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_48]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:38:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.55  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.37/0.55  # and selection function SelectNegativeLiterals.
% 0.37/0.55  #
% 0.37/0.55  # Preprocessing time       : 0.028 s
% 0.37/0.55  # Presaturation interreduction done
% 0.37/0.55  
% 0.37/0.55  # Proof found!
% 0.37/0.55  # SZS status Theorem
% 0.37/0.55  # SZS output start CNFRefutation
% 0.37/0.55  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.37/0.55  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.37/0.55  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.37/0.55  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.37/0.55  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.37/0.55  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.37/0.55  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.37/0.55  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.37/0.55  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.37/0.55  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.37/0.55  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.37/0.55  fof(t81_relat_1, conjecture, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.37/0.55  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 0.37/0.55  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.37/0.55  fof(c_0_14, plain, ![X51, X52]:k1_setfam_1(k2_tarski(X51,X52))=k3_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.37/0.55  fof(c_0_15, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.37/0.55  fof(c_0_16, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.37/0.55  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.37/0.55  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.37/0.55  fof(c_0_19, plain, ![X49, X50]:((k4_xboole_0(X49,k1_tarski(X50))!=X49|~r2_hidden(X50,X49))&(r2_hidden(X50,X49)|k4_xboole_0(X49,k1_tarski(X50))=X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.37/0.55  fof(c_0_20, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.37/0.55  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.55  cnf(c_0_22, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.37/0.55  fof(c_0_23, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.37/0.55  fof(c_0_24, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.37/0.55  fof(c_0_25, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.37/0.55  fof(c_0_26, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.37/0.55  fof(c_0_27, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.37/0.55  fof(c_0_28, plain, ![X12]:k4_xboole_0(k1_xboole_0,X12)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.37/0.55  fof(c_0_29, negated_conjecture, ~(k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t81_relat_1])).
% 0.37/0.55  fof(c_0_30, plain, ![X53, X54, X55, X56, X57, X58]:((((r2_hidden(X55,X53)|~r2_hidden(k4_tarski(X55,X56),X54)|X54!=k6_relat_1(X53)|~v1_relat_1(X54))&(X55=X56|~r2_hidden(k4_tarski(X55,X56),X54)|X54!=k6_relat_1(X53)|~v1_relat_1(X54)))&(~r2_hidden(X57,X53)|X57!=X58|r2_hidden(k4_tarski(X57,X58),X54)|X54!=k6_relat_1(X53)|~v1_relat_1(X54)))&((~r2_hidden(k4_tarski(esk5_2(X53,X54),esk6_2(X53,X54)),X54)|(~r2_hidden(esk5_2(X53,X54),X53)|esk5_2(X53,X54)!=esk6_2(X53,X54))|X54=k6_relat_1(X53)|~v1_relat_1(X54))&((r2_hidden(esk5_2(X53,X54),X53)|r2_hidden(k4_tarski(esk5_2(X53,X54),esk6_2(X53,X54)),X54)|X54=k6_relat_1(X53)|~v1_relat_1(X54))&(esk5_2(X53,X54)=esk6_2(X53,X54)|r2_hidden(k4_tarski(esk5_2(X53,X54),esk6_2(X53,X54)),X54)|X54=k6_relat_1(X53)|~v1_relat_1(X54))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.37/0.55  fof(c_0_31, plain, ![X61, X62, X65, X67, X68]:((~v1_relat_1(X61)|(~r2_hidden(X62,X61)|X62=k4_tarski(esk7_2(X61,X62),esk8_2(X61,X62))))&((r2_hidden(esk9_1(X65),X65)|v1_relat_1(X65))&(esk9_1(X65)!=k4_tarski(X67,X68)|v1_relat_1(X65)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.37/0.55  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.55  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.55  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.37/0.55  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.55  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.55  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.55  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.55  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.37/0.55  cnf(c_0_40, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.55  fof(c_0_41, negated_conjecture, k6_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_42, plain, (r2_hidden(esk5_2(X1,X2),X1)|r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X2)|X2=k6_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.37/0.55  cnf(c_0_43, plain, (r2_hidden(esk9_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.55  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_18]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.37/0.55  cnf(c_0_45, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.37/0.55  cnf(c_0_46, negated_conjecture, (k6_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.37/0.55  cnf(c_0_47, plain, (X1=k6_relat_1(X2)|r2_hidden(k4_tarski(esk5_2(X2,X1),esk6_2(X2,X1)),X1)|r2_hidden(esk5_2(X2,X1),X2)|r2_hidden(esk9_1(X1),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.37/0.55  cnf(c_0_48, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.37/0.55  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])]), c_0_48]), c_0_48]), ['proof']).
% 0.37/0.55  # SZS output end CNFRefutation
% 0.37/0.55  # Proof object total steps             : 50
% 0.37/0.55  # Proof object clause steps            : 21
% 0.37/0.55  # Proof object formula steps           : 29
% 0.37/0.55  # Proof object conjectures             : 5
% 0.37/0.55  # Proof object clause conjectures      : 2
% 0.37/0.55  # Proof object formula conjectures     : 3
% 0.37/0.55  # Proof object initial clauses used    : 14
% 0.37/0.55  # Proof object initial formulas used   : 14
% 0.37/0.55  # Proof object generating inferences   : 3
% 0.37/0.55  # Proof object simplifying inferences  : 25
% 0.37/0.55  # Training examples: 0 positive, 0 negative
% 0.37/0.55  # Parsed axioms                        : 17
% 0.37/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.55  # Initial clauses                      : 29
% 0.37/0.55  # Removed in clause preprocessing      : 9
% 0.37/0.55  # Initial clauses in saturation        : 20
% 0.37/0.55  # Processed clauses                    : 1172
% 0.37/0.55  # ...of these trivial                  : 1
% 0.37/0.55  # ...subsumed                          : 880
% 0.37/0.55  # ...remaining for further processing  : 291
% 0.37/0.55  # Other redundant clauses eliminated   : 76
% 0.37/0.55  # Clauses deleted for lack of memory   : 0
% 0.37/0.55  # Backward-subsumed                    : 1
% 0.37/0.55  # Backward-rewritten                   : 0
% 0.37/0.55  # Generated clauses                    : 13865
% 0.37/0.55  # ...of the previous two non-trivial   : 8887
% 0.37/0.55  # Contextual simplify-reflections      : 0
% 0.37/0.55  # Paramodulations                      : 13782
% 0.37/0.55  # Factorizations                       : 8
% 0.37/0.55  # Equation resolutions                 : 76
% 0.37/0.55  # Propositional unsat checks           : 0
% 0.37/0.55  #    Propositional check models        : 0
% 0.37/0.55  #    Propositional check unsatisfiable : 0
% 0.37/0.55  #    Propositional clauses             : 0
% 0.37/0.55  #    Propositional clauses after purity: 0
% 0.37/0.55  #    Propositional unsat core size     : 0
% 0.37/0.55  #    Propositional preprocessing time  : 0.000
% 0.37/0.55  #    Propositional encoding time       : 0.000
% 0.37/0.55  #    Propositional solver time         : 0.000
% 0.37/0.55  #    Success case prop preproc time    : 0.000
% 0.37/0.55  #    Success case prop encoding time   : 0.000
% 0.37/0.55  #    Success case prop solver time     : 0.000
% 0.37/0.55  # Current number of processed clauses  : 266
% 0.37/0.55  #    Positive orientable unit clauses  : 29
% 0.37/0.55  #    Positive unorientable unit clauses: 0
% 0.37/0.55  #    Negative unit clauses             : 2
% 0.37/0.55  #    Non-unit-clauses                  : 235
% 0.37/0.55  # Current number of unprocessed clauses: 5337
% 0.37/0.55  # ...number of literals in the above   : 23153
% 0.37/0.55  # Current number of archived formulas  : 0
% 0.37/0.55  # Current number of archived clauses   : 30
% 0.37/0.55  # Clause-clause subsumption calls (NU) : 23646
% 0.37/0.55  # Rec. Clause-clause subsumption calls : 16144
% 0.37/0.55  # Non-unit clause-clause subsumptions  : 826
% 0.37/0.55  # Unit Clause-clause subsumption calls : 9
% 0.37/0.55  # Rewrite failures with RHS unbound    : 0
% 0.37/0.55  # BW rewrite match attempts            : 464
% 0.37/0.55  # BW rewrite match successes           : 0
% 0.37/0.55  # Condensation attempts                : 0
% 0.37/0.55  # Condensation successes               : 0
% 0.37/0.55  # Termbank termtop insertions          : 433617
% 0.37/0.55  
% 0.37/0.55  # -------------------------------------------------
% 0.37/0.55  # User time                : 0.187 s
% 0.37/0.55  # System time              : 0.012 s
% 0.37/0.55  # Total time               : 0.200 s
% 0.37/0.55  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

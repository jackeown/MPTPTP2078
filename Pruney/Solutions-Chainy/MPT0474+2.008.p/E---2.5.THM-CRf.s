%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:22 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 107 expanded)
%              Number of clauses        :   17 (  50 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 278 expanded)
%              Number of equality atoms :   33 ( 115 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(t66_relat_1,conjecture,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_9,plain,(
    ! [X21] : k4_xboole_0(k1_xboole_0,X21) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_10,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_11,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X40,X41,X44,X46,X47] :
      ( ( ~ v1_relat_1(X40)
        | ~ r2_hidden(X41,X40)
        | X41 = k4_tarski(esk3_2(X40,X41),esk4_2(X40,X41)) )
      & ( r2_hidden(esk5_1(X44),X44)
        | v1_relat_1(X44) )
      & ( esk5_1(X44) != k4_tarski(X46,X47)
        | v1_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

fof(c_0_20,plain,(
    ! [X48,X49,X50,X51,X52,X53] :
      ( ( ~ r2_hidden(k4_tarski(X50,X51),X49)
        | r2_hidden(k4_tarski(X51,X50),X48)
        | X49 != k4_relat_1(X48)
        | ~ v1_relat_1(X49)
        | ~ v1_relat_1(X48) )
      & ( ~ r2_hidden(k4_tarski(X53,X52),X48)
        | r2_hidden(k4_tarski(X52,X53),X49)
        | X49 != k4_relat_1(X48)
        | ~ v1_relat_1(X49)
        | ~ v1_relat_1(X48) )
      & ( ~ r2_hidden(k4_tarski(esk6_2(X48,X49),esk7_2(X48,X49)),X49)
        | ~ r2_hidden(k4_tarski(esk7_2(X48,X49),esk6_2(X48,X49)),X48)
        | X49 = k4_relat_1(X48)
        | ~ v1_relat_1(X49)
        | ~ v1_relat_1(X48) )
      & ( r2_hidden(k4_tarski(esk6_2(X48,X49),esk7_2(X48,X49)),X49)
        | r2_hidden(k4_tarski(esk7_2(X48,X49),esk6_2(X48,X49)),X48)
        | X49 = k4_relat_1(X48)
        | ~ v1_relat_1(X49)
        | ~ v1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

cnf(c_0_21,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ r2_hidden(esk5_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

fof(c_0_24,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t66_relat_1])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk6_2(X1,X2),esk7_2(X1,X2)),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k4_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_13])])).

fof(c_0_28,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k4_relat_1(X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk7_2(X1,k1_xboole_0),esk6_2(X1,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_30]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.37/0.55  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.37/0.55  #
% 0.37/0.55  # Preprocessing time       : 0.028 s
% 0.37/0.55  # Presaturation interreduction done
% 0.37/0.55  
% 0.37/0.55  # Proof found!
% 0.37/0.55  # SZS status Theorem
% 0.37/0.55  # SZS output start CNFRefutation
% 0.37/0.55  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.37/0.55  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.37/0.55  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.37/0.55  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.37/0.55  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.37/0.55  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 0.37/0.55  fof(t66_relat_1, conjecture, k4_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 0.37/0.55  fof(c_0_7, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.37/0.55  cnf(c_0_8, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.37/0.55  fof(c_0_9, plain, ![X21]:k4_xboole_0(k1_xboole_0,X21)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.37/0.55  fof(c_0_10, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.37/0.55  fof(c_0_11, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.37/0.55  cnf(c_0_12, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_8])).
% 0.37/0.55  cnf(c_0_13, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.37/0.55  fof(c_0_14, plain, ![X40, X41, X44, X46, X47]:((~v1_relat_1(X40)|(~r2_hidden(X41,X40)|X41=k4_tarski(esk3_2(X40,X41),esk4_2(X40,X41))))&((r2_hidden(esk5_1(X44),X44)|v1_relat_1(X44))&(esk5_1(X44)!=k4_tarski(X46,X47)|v1_relat_1(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.37/0.55  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.37/0.55  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.55  cnf(c_0_17, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.37/0.55  cnf(c_0_18, plain, (r2_hidden(esk5_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.37/0.55  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.37/0.55  fof(c_0_20, plain, ![X48, X49, X50, X51, X52, X53]:(((~r2_hidden(k4_tarski(X50,X51),X49)|r2_hidden(k4_tarski(X51,X50),X48)|X49!=k4_relat_1(X48)|~v1_relat_1(X49)|~v1_relat_1(X48))&(~r2_hidden(k4_tarski(X53,X52),X48)|r2_hidden(k4_tarski(X52,X53),X49)|X49!=k4_relat_1(X48)|~v1_relat_1(X49)|~v1_relat_1(X48)))&((~r2_hidden(k4_tarski(esk6_2(X48,X49),esk7_2(X48,X49)),X49)|~r2_hidden(k4_tarski(esk7_2(X48,X49),esk6_2(X48,X49)),X48)|X49=k4_relat_1(X48)|~v1_relat_1(X49)|~v1_relat_1(X48))&(r2_hidden(k4_tarski(esk6_2(X48,X49),esk7_2(X48,X49)),X49)|r2_hidden(k4_tarski(esk7_2(X48,X49),esk6_2(X48,X49)),X48)|X49=k4_relat_1(X48)|~v1_relat_1(X49)|~v1_relat_1(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 0.37/0.55  cnf(c_0_21, plain, (v1_relat_1(k1_xboole_0)|~r2_hidden(esk5_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.37/0.55  cnf(c_0_22, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_12, c_0_19])).
% 0.37/0.55  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 0.37/0.55  fof(c_0_24, negated_conjecture, ~(k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t66_relat_1])).
% 0.37/0.55  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk6_2(X1,X2),esk7_2(X1,X2)),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k4_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.55  cnf(c_0_26, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.37/0.55  cnf(c_0_27, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_13])])).
% 0.37/0.55  fof(c_0_28, negated_conjecture, k4_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_24])).
% 0.37/0.55  cnf(c_0_29, plain, (k4_relat_1(X1)=k1_xboole_0|r2_hidden(k4_tarski(esk7_2(X1,k1_xboole_0),esk6_2(X1,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.37/0.55  cnf(c_0_30, negated_conjecture, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.55  cnf(c_0_31, plain, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_30]), c_0_27]), ['proof']).
% 0.37/0.55  # SZS output end CNFRefutation
% 0.37/0.55  # Proof object total steps             : 32
% 0.37/0.55  # Proof object clause steps            : 17
% 0.37/0.55  # Proof object formula steps           : 15
% 0.37/0.55  # Proof object conjectures             : 4
% 0.37/0.55  # Proof object clause conjectures      : 1
% 0.37/0.55  # Proof object formula conjectures     : 3
% 0.37/0.55  # Proof object initial clauses used    : 7
% 0.37/0.55  # Proof object initial formulas used   : 7
% 0.37/0.55  # Proof object generating inferences   : 8
% 0.37/0.55  # Proof object simplifying inferences  : 8
% 0.37/0.55  # Training examples: 0 positive, 0 negative
% 0.37/0.55  # Parsed axioms                        : 14
% 0.37/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.55  # Initial clauses                      : 28
% 0.37/0.55  # Removed in clause preprocessing      : 3
% 0.37/0.55  # Initial clauses in saturation        : 25
% 0.37/0.55  # Processed clauses                    : 1909
% 0.37/0.55  # ...of these trivial                  : 7
% 0.37/0.55  # ...subsumed                          : 1499
% 0.37/0.55  # ...remaining for further processing  : 403
% 0.37/0.55  # Other redundant clauses eliminated   : 10
% 0.37/0.55  # Clauses deleted for lack of memory   : 0
% 0.37/0.55  # Backward-subsumed                    : 12
% 0.37/0.55  # Backward-rewritten                   : 55
% 0.37/0.55  # Generated clauses                    : 12743
% 0.37/0.55  # ...of the previous two non-trivial   : 11533
% 0.37/0.55  # Contextual simplify-reflections      : 11
% 0.37/0.55  # Paramodulations                      : 12717
% 0.37/0.55  # Factorizations                       : 16
% 0.37/0.55  # Equation resolutions                 : 10
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
% 0.37/0.55  # Current number of processed clauses  : 303
% 0.37/0.55  #    Positive orientable unit clauses  : 14
% 0.37/0.55  #    Positive unorientable unit clauses: 1
% 0.37/0.55  #    Negative unit clauses             : 3
% 0.37/0.55  #    Non-unit-clauses                  : 285
% 0.37/0.55  # Current number of unprocessed clauses: 9656
% 0.37/0.55  # ...number of literals in the above   : 36861
% 0.37/0.55  # Current number of archived formulas  : 0
% 0.37/0.55  # Current number of archived clauses   : 95
% 0.37/0.55  # Clause-clause subsumption calls (NU) : 17688
% 0.37/0.55  # Rec. Clause-clause subsumption calls : 10858
% 0.37/0.55  # Non-unit clause-clause subsumptions  : 866
% 0.37/0.55  # Unit Clause-clause subsumption calls : 325
% 0.37/0.55  # Rewrite failures with RHS unbound    : 0
% 0.37/0.55  # BW rewrite match attempts            : 79
% 0.37/0.55  # BW rewrite match successes           : 20
% 0.37/0.55  # Condensation attempts                : 0
% 0.37/0.55  # Condensation successes               : 0
% 0.37/0.55  # Termbank termtop insertions          : 238896
% 0.37/0.55  
% 0.37/0.55  # -------------------------------------------------
% 0.37/0.55  # User time                : 0.196 s
% 0.37/0.55  # System time              : 0.012 s
% 0.37/0.55  # Total time               : 0.208 s
% 0.37/0.55  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

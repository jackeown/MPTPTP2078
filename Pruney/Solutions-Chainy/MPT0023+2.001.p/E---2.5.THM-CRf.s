%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:51 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   50 (4879 expanded)
%              Number of clauses        :   45 (2796 expanded)
%              Number of leaves         :    2 (1041 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 (32282 expanded)
%              Number of equality atoms :   51 (9586 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t16_xboole_1,conjecture,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(c_0_2,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_3,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_4,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_5,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_6,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_3])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_15,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X2)
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_6])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_6])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X2)
    | ~ r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_11])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X1)
    | r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X1) ),
    inference(ef,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X4)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X3)
    | r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_21,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(X3,X2)
    | ~ r2_hidden(esk1_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2),k3_xboole_0(X3,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4)) = k3_xboole_0(k3_xboole_0(X2,X3),X4)
    | r2_hidden(esk1_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_17])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,X1)
    | ~ r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,k3_xboole_0(X1,X2)),X2) ),
    inference(ef,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X1),X2)) = k3_xboole_0(k3_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X2),X1)) = k3_xboole_0(k3_xboole_0(X3,X2),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1)) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_26]),c_0_25])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_14])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t16_xboole_1])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4)) = k3_xboole_0(k3_xboole_0(X2,X3),X4)
    | r2_hidden(esk1_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_17])).

cnf(c_0_34,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4))) = k3_xboole_0(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,k3_xboole_0(X3,X4))),X4) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_31]),c_0_31])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,X2)
    | r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_31])).

fof(c_0_38,negated_conjecture,(
    k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk4_0) != k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

cnf(c_0_39,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X3),X2)) = k3_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_34]),c_0_34])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_35])).

cnf(c_0_42,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk4_0) != k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_34]),c_0_41])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_16])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk4_0)) != k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_44]),c_0_44]),c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.76/1.96  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 1.76/1.96  # and selection function SelectVGNonCR.
% 1.76/1.96  #
% 1.76/1.96  # Preprocessing time       : 0.028 s
% 1.76/1.96  # Presaturation interreduction done
% 1.76/1.96  
% 1.76/1.96  # Proof found!
% 1.76/1.96  # SZS status Theorem
% 1.76/1.96  # SZS output start CNFRefutation
% 1.76/1.96  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.76/1.96  fof(t16_xboole_1, conjecture, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.76/1.96  fof(c_0_2, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.76/1.96  cnf(c_0_3, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 1.76/1.96  cnf(c_0_4, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 1.76/1.96  cnf(c_0_5, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 1.76/1.96  cnf(c_0_6, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_3])).
% 1.76/1.96  cnf(c_0_7, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 1.76/1.96  cnf(c_0_8, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 1.76/1.96  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_4])).
% 1.76/1.96  cnf(c_0_10, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_6])).
% 1.76/1.96  cnf(c_0_11, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_7])).
% 1.76/1.96  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_8])).
% 1.76/1.96  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X3,X4)|r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X4)|r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_9, c_0_3])).
% 1.76/1.96  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 1.76/1.96  cnf(c_0_15, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=X3|~r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X2)|~r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 1.76/1.96  cnf(c_0_16, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_12, c_0_6])).
% 1.76/1.96  cnf(c_0_17, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_9, c_0_6])).
% 1.76/1.96  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X3,X4)|~r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X4)|~r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X3)|~r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X2)|~r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_5, c_0_11])).
% 1.76/1.96  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X3,X1)|r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X1)), inference(ef,[status(thm)],[c_0_13])).
% 1.76/1.96  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X3,X4)|r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X3)|r2_hidden(esk1_3(X3,X4,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_12, c_0_14])).
% 1.76/1.96  cnf(c_0_21, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(X3,X2)|~r2_hidden(esk1_3(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2),k3_xboole_0(X3,X2)),X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.76/1.96  cnf(c_0_22, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))=k3_xboole_0(k3_xboole_0(X2,X3),X4)|r2_hidden(esk1_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X3)), inference(spm,[status(thm)],[c_0_12, c_0_17])).
% 1.76/1.96  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X3,X1)|~r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X3)|~r2_hidden(esk1_3(X3,X1,k3_xboole_0(X1,X2)),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 1.76/1.96  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X3)|r2_hidden(esk1_3(X2,X3,k3_xboole_0(X1,X2)),X2)), inference(ef,[status(thm)],[c_0_20])).
% 1.76/1.96  cnf(c_0_25, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X1),X2))=k3_xboole_0(k3_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.76/1.96  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 1.76/1.96  cnf(c_0_27, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.76/1.96  cnf(c_0_28, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X3,X2),X1))=k3_xboole_0(k3_xboole_0(X3,X2),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.76/1.96  cnf(c_0_29, plain, (k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X3,X1))=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.76/1.96  cnf(c_0_30, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_26]), c_0_25])).
% 1.76/1.96  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_14])).
% 1.76/1.96  fof(c_0_32, negated_conjecture, ~(![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t16_xboole_1])).
% 1.76/1.96  cnf(c_0_33, plain, (k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4))=k3_xboole_0(k3_xboole_0(X2,X3),X4)|r2_hidden(esk1_3(X1,k3_xboole_0(k3_xboole_0(X2,X3),X4),k3_xboole_0(k3_xboole_0(X2,X3),X4)),X2)), inference(spm,[status(thm)],[c_0_9, c_0_17])).
% 1.76/1.96  cnf(c_0_34, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 1.76/1.96  cnf(c_0_35, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))=k3_xboole_0(X2,k3_xboole_0(X3,X4))|r2_hidden(esk1_3(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)),k3_xboole_0(X2,k3_xboole_0(X3,X4))),X4)), inference(spm,[status(thm)],[c_0_12, c_0_16])).
% 1.76/1.96  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_31]), c_0_31])).
% 1.76/1.96  cnf(c_0_37, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,X2)|r2_hidden(esk1_3(k3_xboole_0(X1,X2),X3,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_9, c_0_31])).
% 1.76/1.96  fof(c_0_38, negated_conjecture, k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk4_0)!=k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 1.76/1.96  cnf(c_0_39, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X3),X2))=k3_xboole_0(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_21, c_0_33])).
% 1.76/1.96  cnf(c_0_40, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_34]), c_0_34])).
% 1.76/1.96  cnf(c_0_41, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_10, c_0_35])).
% 1.76/1.96  cnf(c_0_42, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.76/1.96  cnf(c_0_43, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk4_0)!=k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.76/1.96  cnf(c_0_44, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_34]), c_0_41])).
% 1.76/1.96  cnf(c_0_45, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_10, c_0_16])).
% 1.76/1.96  cnf(c_0_46, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.76/1.96  cnf(c_0_47, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk4_0))!=k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 1.76/1.96  cnf(c_0_48, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_44]), c_0_44]), c_0_46])).
% 1.76/1.96  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])]), ['proof']).
% 1.76/1.96  # SZS output end CNFRefutation
% 1.76/1.96  # Proof object total steps             : 50
% 1.76/1.96  # Proof object clause steps            : 45
% 1.76/1.96  # Proof object formula steps           : 5
% 1.76/1.96  # Proof object conjectures             : 6
% 1.76/1.96  # Proof object clause conjectures      : 3
% 1.76/1.96  # Proof object formula conjectures     : 3
% 1.76/1.96  # Proof object initial clauses used    : 7
% 1.76/1.96  # Proof object initial formulas used   : 2
% 1.76/1.96  # Proof object generating inferences   : 36
% 1.76/1.96  # Proof object simplifying inferences  : 15
% 1.76/1.96  # Training examples: 0 positive, 0 negative
% 1.76/1.96  # Parsed axioms                        : 2
% 1.76/1.96  # Removed by relevancy pruning/SinE    : 0
% 1.76/1.96  # Initial clauses                      : 7
% 1.76/1.96  # Removed in clause preprocessing      : 0
% 1.76/1.96  # Initial clauses in saturation        : 7
% 1.76/1.96  # Processed clauses                    : 7842
% 1.76/1.96  # ...of these trivial                  : 929
% 1.76/1.96  # ...subsumed                          : 6364
% 1.76/1.96  # ...remaining for further processing  : 549
% 1.76/1.96  # Other redundant clauses eliminated   : 3
% 1.76/1.96  # Clauses deleted for lack of memory   : 0
% 1.76/1.96  # Backward-subsumed                    : 2
% 1.76/1.96  # Backward-rewritten                   : 397
% 1.76/1.96  # Generated clauses                    : 196500
% 1.76/1.96  # ...of the previous two non-trivial   : 175741
% 1.76/1.96  # Contextual simplify-reflections      : 9
% 1.76/1.96  # Paramodulations                      : 196238
% 1.76/1.96  # Factorizations                       : 196
% 1.76/1.96  # Equation resolutions                 : 66
% 1.76/1.96  # Propositional unsat checks           : 0
% 1.76/1.96  #    Propositional check models        : 0
% 1.76/1.96  #    Propositional check unsatisfiable : 0
% 1.76/1.96  #    Propositional clauses             : 0
% 1.76/1.96  #    Propositional clauses after purity: 0
% 1.76/1.96  #    Propositional unsat core size     : 0
% 1.76/1.96  #    Propositional preprocessing time  : 0.000
% 1.76/1.96  #    Propositional encoding time       : 0.000
% 1.76/1.96  #    Propositional solver time         : 0.000
% 1.76/1.96  #    Success case prop preproc time    : 0.000
% 1.76/1.96  #    Success case prop encoding time   : 0.000
% 1.76/1.96  #    Success case prop solver time     : 0.000
% 1.76/1.96  # Current number of processed clauses  : 143
% 1.76/1.96  #    Positive orientable unit clauses  : 12
% 1.76/1.96  #    Positive unorientable unit clauses: 4
% 1.76/1.96  #    Negative unit clauses             : 0
% 1.76/1.96  #    Non-unit-clauses                  : 127
% 1.76/1.96  # Current number of unprocessed clauses: 165297
% 1.76/1.96  # ...number of literals in the above   : 388279
% 1.76/1.96  # Current number of archived formulas  : 0
% 1.76/1.96  # Current number of archived clauses   : 406
% 1.76/1.96  # Clause-clause subsumption calls (NU) : 257085
% 1.76/1.96  # Rec. Clause-clause subsumption calls : 235663
% 1.76/1.96  # Non-unit clause-clause subsumptions  : 6337
% 1.76/1.96  # Unit Clause-clause subsumption calls : 4820
% 1.76/1.96  # Rewrite failures with RHS unbound    : 0
% 1.76/1.96  # BW rewrite match attempts            : 4671
% 1.76/1.96  # BW rewrite match successes           : 1595
% 1.76/1.96  # Condensation attempts                : 0
% 1.76/1.96  # Condensation successes               : 0
% 1.76/1.96  # Termbank termtop insertions          : 3058350
% 1.76/1.97  
% 1.76/1.97  # -------------------------------------------------
% 1.76/1.97  # User time                : 1.551 s
% 1.76/1.97  # System time              : 0.072 s
% 1.76/1.97  # Total time               : 1.623 s
% 1.76/1.97  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------

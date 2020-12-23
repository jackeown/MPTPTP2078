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
% DateTime   : Thu Dec  3 10:43:20 EST 2020

% Result     : Theorem 25.30s
% Output     : CNFRefutation 25.30s
% Verified   : 
% Statistics : Number of formulae       :   49 (  61 expanded)
%              Number of clauses        :   32 (  32 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  168 ( 303 expanded)
%              Number of equality atoms :   54 (  94 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t99_zfmisc_1,conjecture,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X23,X22)
        | r1_tarski(X23,X21)
        | X22 != k1_zfmisc_1(X21) )
      & ( ~ r1_tarski(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k1_zfmisc_1(X21) )
      & ( ~ r2_hidden(esk2_2(X25,X26),X26)
        | ~ r1_tarski(esk2_2(X25,X26),X25)
        | X26 = k1_zfmisc_1(X25) )
      & ( r2_hidden(esk2_2(X25,X26),X26)
        | r1_tarski(esk2_2(X25,X26),X25)
        | X26 = k1_zfmisc_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_13,plain,(
    ! [X28,X29,X30,X32,X33,X34,X35,X37] :
      ( ( r2_hidden(X30,esk3_3(X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k3_tarski(X28) )
      & ( r2_hidden(esk3_3(X28,X29,X30),X28)
        | ~ r2_hidden(X30,X29)
        | X29 != k3_tarski(X28) )
      & ( ~ r2_hidden(X32,X33)
        | ~ r2_hidden(X33,X28)
        | r2_hidden(X32,X29)
        | X29 != k3_tarski(X28) )
      & ( ~ r2_hidden(esk4_2(X34,X35),X35)
        | ~ r2_hidden(esk4_2(X34,X35),X37)
        | ~ r2_hidden(X37,X34)
        | X35 = k3_tarski(X34) )
      & ( r2_hidden(esk4_2(X34,X35),esk5_2(X34,X35))
        | r2_hidden(esk4_2(X34,X35),X35)
        | X35 = k3_tarski(X34) )
      & ( r2_hidden(esk5_2(X34,X35),X34)
        | r2_hidden(esk4_2(X34,X35),X35)
        | X35 = k3_tarski(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_16,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(esk4_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,esk3_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_34,plain,
    ( X1 = k3_tarski(k1_zfmisc_1(X2))
    | r1_tarski(esk5_2(k1_zfmisc_1(X2),X1),X2)
    | r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( X1 = k3_tarski(X2)
    | ~ r2_hidden(esk3_3(X3,k3_tarski(X3),esk4_2(X2,X1)),X2)
    | ~ r2_hidden(esk4_2(X2,X1),k3_tarski(X3))
    | ~ r2_hidden(esk4_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(esk3_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k3_tarski(k1_zfmisc_1(X2)))
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t99_zfmisc_1])).

cnf(c_0_40,plain,
    ( X1 = k3_tarski(k1_zfmisc_1(X2))
    | r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,esk5_2(k1_zfmisc_1(X2),X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(esk4_2(X1,X2),esk5_2(X1,X2))
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( X1 = k3_tarski(X2)
    | ~ r2_hidden(esk4_2(X2,X1),k3_tarski(X2))
    | ~ r2_hidden(esk4_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k3_tarski(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,negated_conjecture,(
    k3_tarski(k1_zfmisc_1(esk6_0)) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_45,plain,
    ( X1 = k3_tarski(k1_zfmisc_1(X2))
    | r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1)
    | r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( X1 = k3_tarski(k1_zfmisc_1(X2))
    | ~ r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1)
    | ~ r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(esk6_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_45,c_0_46,c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:30:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 25.30/25.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 25.30/25.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 25.30/25.52  #
% 25.30/25.52  # Preprocessing time       : 0.028 s
% 25.30/25.52  # Presaturation interreduction done
% 25.30/25.52  # SatCheck found unsatisfiable ground set
% 25.30/25.52  
% 25.30/25.52  # Proof found!
% 25.30/25.52  # SZS status Theorem
% 25.30/25.52  # SZS output start CNFRefutation
% 25.30/25.52  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 25.30/25.52  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 25.30/25.52  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 25.30/25.52  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 25.30/25.52  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 25.30/25.52  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 25.30/25.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 25.30/25.52  fof(t99_zfmisc_1, conjecture, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 25.30/25.52  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 25.30/25.52  fof(c_0_9, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 25.30/25.52  cnf(c_0_10, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 25.30/25.52  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 25.30/25.52  fof(c_0_12, plain, ![X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X23,X22)|r1_tarski(X23,X21)|X22!=k1_zfmisc_1(X21))&(~r1_tarski(X24,X21)|r2_hidden(X24,X22)|X22!=k1_zfmisc_1(X21)))&((~r2_hidden(esk2_2(X25,X26),X26)|~r1_tarski(esk2_2(X25,X26),X25)|X26=k1_zfmisc_1(X25))&(r2_hidden(esk2_2(X25,X26),X26)|r1_tarski(esk2_2(X25,X26),X25)|X26=k1_zfmisc_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 25.30/25.52  fof(c_0_13, plain, ![X28, X29, X30, X32, X33, X34, X35, X37]:((((r2_hidden(X30,esk3_3(X28,X29,X30))|~r2_hidden(X30,X29)|X29!=k3_tarski(X28))&(r2_hidden(esk3_3(X28,X29,X30),X28)|~r2_hidden(X30,X29)|X29!=k3_tarski(X28)))&(~r2_hidden(X32,X33)|~r2_hidden(X33,X28)|r2_hidden(X32,X29)|X29!=k3_tarski(X28)))&((~r2_hidden(esk4_2(X34,X35),X35)|(~r2_hidden(esk4_2(X34,X35),X37)|~r2_hidden(X37,X34))|X35=k3_tarski(X34))&((r2_hidden(esk4_2(X34,X35),esk5_2(X34,X35))|r2_hidden(esk4_2(X34,X35),X35)|X35=k3_tarski(X34))&(r2_hidden(esk5_2(X34,X35),X34)|r2_hidden(esk4_2(X34,X35),X35)|X35=k3_tarski(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 25.30/25.52  cnf(c_0_14, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 25.30/25.52  fof(c_0_15, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 25.30/25.52  fof(c_0_16, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 25.30/25.52  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 25.30/25.52  cnf(c_0_18, plain, (r2_hidden(X1,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 25.30/25.52  cnf(c_0_19, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 25.30/25.52  cnf(c_0_20, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 25.30/25.52  fof(c_0_21, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 25.30/25.52  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_14])).
% 25.30/25.52  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 25.30/25.52  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 25.30/25.52  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 25.30/25.52  cnf(c_0_26, plain, (r2_hidden(esk5_2(X1,X2),X1)|r2_hidden(esk4_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 25.30/25.52  cnf(c_0_27, plain, (X2=k3_tarski(X1)|~r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(esk4_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 25.30/25.52  cnf(c_0_28, plain, (r2_hidden(X1,esk3_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_18])).
% 25.30/25.52  cnf(c_0_29, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 25.30/25.52  cnf(c_0_30, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_19])).
% 25.30/25.52  cnf(c_0_31, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_20])).
% 25.30/25.52  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 25.30/25.52  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 25.30/25.52  cnf(c_0_34, plain, (X1=k3_tarski(k1_zfmisc_1(X2))|r1_tarski(esk5_2(k1_zfmisc_1(X2),X1),X2)|r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 25.30/25.52  cnf(c_0_35, plain, (X1=k3_tarski(X2)|~r2_hidden(esk3_3(X3,k3_tarski(X3),esk4_2(X2,X1)),X2)|~r2_hidden(esk4_2(X2,X1),k3_tarski(X3))|~r2_hidden(esk4_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 25.30/25.52  cnf(c_0_36, plain, (r2_hidden(esk3_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_29])).
% 25.30/25.52  cnf(c_0_37, plain, (r2_hidden(X1,k3_tarski(k1_zfmisc_1(X2)))|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 25.30/25.52  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 25.30/25.52  fof(c_0_39, negated_conjecture, ~(![X1]:k3_tarski(k1_zfmisc_1(X1))=X1), inference(assume_negation,[status(cth)],[t99_zfmisc_1])).
% 25.30/25.52  cnf(c_0_40, plain, (X1=k3_tarski(k1_zfmisc_1(X2))|r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1)|r2_hidden(X3,X2)|~r2_hidden(X3,esk5_2(k1_zfmisc_1(X2),X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 25.30/25.52  cnf(c_0_41, plain, (r2_hidden(esk4_2(X1,X2),esk5_2(X1,X2))|r2_hidden(esk4_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 25.30/25.52  cnf(c_0_42, plain, (X1=k3_tarski(X2)|~r2_hidden(esk4_2(X2,X1),k3_tarski(X2))|~r2_hidden(esk4_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 25.30/25.52  cnf(c_0_43, plain, (r2_hidden(X1,k3_tarski(k1_zfmisc_1(X2)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 25.30/25.52  fof(c_0_44, negated_conjecture, k3_tarski(k1_zfmisc_1(esk6_0))!=esk6_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 25.30/25.52  cnf(c_0_45, plain, (X1=k3_tarski(k1_zfmisc_1(X2))|r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1)|r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 25.30/25.52  cnf(c_0_46, plain, (X1=k3_tarski(k1_zfmisc_1(X2))|~r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X1)|~r2_hidden(esk4_2(k1_zfmisc_1(X2),X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 25.30/25.52  cnf(c_0_47, negated_conjecture, (k3_tarski(k1_zfmisc_1(esk6_0))!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 25.30/25.52  cnf(c_0_48, plain, ($false), inference(cdclpropres,[status(thm)],[c_0_45, c_0_46, c_0_47]), ['proof']).
% 25.30/25.52  # SZS output end CNFRefutation
% 25.30/25.52  # Proof object total steps             : 49
% 25.30/25.52  # Proof object clause steps            : 32
% 25.30/25.52  # Proof object formula steps           : 17
% 25.30/25.52  # Proof object conjectures             : 4
% 25.30/25.52  # Proof object clause conjectures      : 1
% 25.30/25.52  # Proof object formula conjectures     : 3
% 25.30/25.52  # Proof object initial clauses used    : 14
% 25.30/25.52  # Proof object initial formulas used   : 8
% 25.30/25.52  # Proof object generating inferences   : 9
% 25.30/25.52  # Proof object simplifying inferences  : 9
% 25.30/25.52  # Training examples: 0 positive, 0 negative
% 25.30/25.52  # Parsed axioms                        : 8
% 25.30/25.52  # Removed by relevancy pruning/SinE    : 0
% 25.30/25.52  # Initial clauses                      : 24
% 25.30/25.52  # Removed in clause preprocessing      : 1
% 25.30/25.52  # Initial clauses in saturation        : 23
% 25.30/25.52  # Processed clauses                    : 16591
% 25.30/25.52  # ...of these trivial                  : 2
% 25.30/25.52  # ...subsumed                          : 11589
% 25.30/25.52  # ...remaining for further processing  : 5000
% 25.30/25.52  # Other redundant clauses eliminated   : 377
% 25.30/25.52  # Clauses deleted for lack of memory   : 0
% 25.30/25.52  # Backward-subsumed                    : 425
% 25.30/25.52  # Backward-rewritten                   : 543
% 25.30/25.52  # Generated clauses                    : 1746466
% 25.30/25.52  # ...of the previous two non-trivial   : 1744127
% 25.30/25.52  # Contextual simplify-reflections      : 186
% 25.30/25.52  # Paramodulations                      : 1745803
% 25.30/25.52  # Factorizations                       : 286
% 25.30/25.52  # Equation resolutions                 : 377
% 25.30/25.52  # Propositional unsat checks           : 1
% 25.30/25.52  #    Propositional check models        : 0
% 25.30/25.52  #    Propositional check unsatisfiable : 1
% 25.30/25.52  #    Propositional clauses             : 1724092
% 25.30/25.52  #    Propositional clauses after purity: 19300
% 25.30/25.52  #    Propositional unsat core size     : 3
% 25.30/25.52  #    Propositional preprocessing time  : 0.000
% 25.30/25.52  #    Propositional encoding time       : 3.983
% 25.30/25.52  #    Propositional solver time         : 0.115
% 25.30/25.52  #    Success case prop preproc time    : 0.000
% 25.30/25.52  #    Success case prop encoding time   : 3.983
% 25.30/25.52  #    Success case prop solver time     : 0.115
% 25.30/25.52  # Current number of processed clauses  : 4000
% 25.30/25.52  #    Positive orientable unit clauses  : 5
% 25.30/25.52  #    Positive unorientable unit clauses: 0
% 25.30/25.52  #    Negative unit clauses             : 1
% 25.30/25.52  #    Non-unit-clauses                  : 3994
% 25.30/25.52  # Current number of unprocessed clauses: 1720092
% 25.30/25.52  # ...number of literals in the above   : 10153503
% 25.30/25.52  # Current number of archived formulas  : 0
% 25.30/25.52  # Current number of archived clauses   : 991
% 25.30/25.52  # Clause-clause subsumption calls (NU) : 1338976
% 25.30/25.52  # Rec. Clause-clause subsumption calls : 742562
% 25.30/25.52  # Non-unit clause-clause subsumptions  : 12196
% 25.30/25.52  # Unit Clause-clause subsumption calls : 2936
% 25.30/25.52  # Rewrite failures with RHS unbound    : 0
% 25.30/25.52  # BW rewrite match attempts            : 338
% 25.30/25.52  # BW rewrite match successes           : 3
% 25.30/25.52  # Condensation attempts                : 0
% 25.30/25.52  # Condensation successes               : 0
% 25.30/25.52  # Termbank termtop insertions          : 110529052
% 25.38/25.60  
% 25.38/25.60  # -------------------------------------------------
% 25.38/25.60  # User time                : 24.248 s
% 25.38/25.60  # System time              : 0.984 s
% 25.38/25.60  # Total time               : 25.232 s
% 25.38/25.60  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

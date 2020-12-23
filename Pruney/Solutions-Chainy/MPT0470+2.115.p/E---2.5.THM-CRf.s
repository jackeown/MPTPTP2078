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
% DateTime   : Thu Dec  3 10:49:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 480 expanded)
%              Number of clauses        :   33 ( 210 expanded)
%              Number of leaves         :    8 ( 132 expanded)
%              Depth                    :   15
%              Number of atoms          :  182 (1430 expanded)
%              Number of equality atoms :   37 ( 284 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_8,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_10,plain,(
    ! [X14] : r1_xboole_0(X14,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X15,X16,X19,X21,X22] :
      ( ( ~ v1_relat_1(X15)
        | ~ r2_hidden(X16,X15)
        | X16 = k4_tarski(esk2_2(X15,X16),esk3_2(X15,X16)) )
      & ( r2_hidden(esk4_1(X19),X19)
        | v1_relat_1(X19) )
      & ( esk4_1(X19) != k4_tarski(X21,X22)
        | v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_15,plain,(
    ! [X23,X24,X25,X26,X27,X29,X30,X31,X34] :
      ( ( r2_hidden(k4_tarski(X26,esk5_5(X23,X24,X25,X26,X27)),X23)
        | ~ r2_hidden(k4_tarski(X26,X27),X25)
        | X25 != k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk5_5(X23,X24,X25,X26,X27),X27),X24)
        | ~ r2_hidden(k4_tarski(X26,X27),X25)
        | X25 != k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X29,X31),X23)
        | ~ r2_hidden(k4_tarski(X31,X30),X24)
        | r2_hidden(k4_tarski(X29,X30),X25)
        | X25 != k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk7_3(X23,X24,X25)),X25)
        | ~ r2_hidden(k4_tarski(esk6_3(X23,X24,X25),X34),X23)
        | ~ r2_hidden(k4_tarski(X34,esk7_3(X23,X24,X25)),X24)
        | X25 = k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk8_3(X23,X24,X25)),X23)
        | r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk7_3(X23,X24,X25)),X25)
        | X25 = k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk8_3(X23,X24,X25),esk7_3(X23,X24,X25)),X24)
        | r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk7_3(X23,X24,X25)),X25)
        | X25 = k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk8_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk5_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_17])).

fof(c_0_22,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X38)
      | ~ v1_relat_1(X39)
      | ~ v1_relat_1(X40)
      | k5_relat_1(k5_relat_1(X38,X39),X40) = k5_relat_1(X38,k5_relat_1(X39,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_23,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk6_3(k1_xboole_0,X2,X1),esk7_3(k1_xboole_0,X2,X1)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( X1 != k5_relat_1(k3_xboole_0(X2,X3),X4)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(k4_tarski(X5,X6),X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_23]),c_0_19])])).

cnf(c_0_27,plain,
    ( ~ v1_relat_1(k5_relat_1(k3_xboole_0(X1,X2),X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(k3_xboole_0(X1,X2),X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1(X1,X2)) = k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

fof(c_0_30,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ v1_relat_1(X37)
      | v1_relat_1(k5_relat_1(X36,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_31,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_12]),c_0_13])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_19])])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
      | k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_35,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( X1 != k5_relat_1(X2,k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_35])).

cnf(c_0_40,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X2,k5_relat_1(k1_xboole_0,X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( v1_relat_1(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_19])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_19])])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
    | k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_23]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_38])]),c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_26]),c_0_38])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_38,c_0_48]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.027 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.43  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.43  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.43  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.19/0.43  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.19/0.43  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.19/0.43  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.19/0.43  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.43  fof(c_0_8, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.43  fof(c_0_9, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.43  fof(c_0_10, plain, ![X14]:r1_xboole_0(X14,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.43  cnf(c_0_11, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.43  cnf(c_0_12, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.43  cnf(c_0_13, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  fof(c_0_14, plain, ![X15, X16, X19, X21, X22]:((~v1_relat_1(X15)|(~r2_hidden(X16,X15)|X16=k4_tarski(esk2_2(X15,X16),esk3_2(X15,X16))))&((r2_hidden(esk4_1(X19),X19)|v1_relat_1(X19))&(esk4_1(X19)!=k4_tarski(X21,X22)|v1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.19/0.43  fof(c_0_15, plain, ![X23, X24, X25, X26, X27, X29, X30, X31, X34]:((((r2_hidden(k4_tarski(X26,esk5_5(X23,X24,X25,X26,X27)),X23)|~r2_hidden(k4_tarski(X26,X27),X25)|X25!=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk5_5(X23,X24,X25,X26,X27),X27),X24)|~r2_hidden(k4_tarski(X26,X27),X25)|X25!=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23)))&(~r2_hidden(k4_tarski(X29,X31),X23)|~r2_hidden(k4_tarski(X31,X30),X24)|r2_hidden(k4_tarski(X29,X30),X25)|X25!=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23)))&((~r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk7_3(X23,X24,X25)),X25)|(~r2_hidden(k4_tarski(esk6_3(X23,X24,X25),X34),X23)|~r2_hidden(k4_tarski(X34,esk7_3(X23,X24,X25)),X24))|X25=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23))&((r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk8_3(X23,X24,X25)),X23)|r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk7_3(X23,X24,X25)),X25)|X25=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk8_3(X23,X24,X25),esk7_3(X23,X24,X25)),X24)|r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk7_3(X23,X24,X25)),X25)|X25=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.19/0.43  cnf(c_0_16, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.19/0.43  cnf(c_0_17, plain, (r2_hidden(esk4_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_18, plain, (r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk8_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_19, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.43  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,esk5_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_21, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_17])).
% 0.19/0.43  fof(c_0_22, plain, ![X38, X39, X40]:(~v1_relat_1(X38)|(~v1_relat_1(X39)|(~v1_relat_1(X40)|k5_relat_1(k5_relat_1(X38,X39),X40)=k5_relat_1(X38,k5_relat_1(X39,X40))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.19/0.43  cnf(c_0_23, plain, (X1=k5_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk6_3(k1_xboole_0,X2,X1),esk7_3(k1_xboole_0,X2,X1)),X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_18]), c_0_19])])).
% 0.19/0.43  cnf(c_0_24, plain, (X1!=k5_relat_1(k3_xboole_0(X2,X3),X4)|~v1_relat_1(X1)|~v1_relat_1(X4)|~r2_hidden(k4_tarski(X5,X6),X1)|~r1_xboole_0(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_20]), c_0_21])).
% 0.19/0.43  cnf(c_0_25, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.43  cnf(c_0_26, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_23]), c_0_19])])).
% 0.19/0.43  cnf(c_0_27, plain, (~v1_relat_1(k5_relat_1(k3_xboole_0(X1,X2),X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X5),k5_relat_1(k3_xboole_0(X1,X2),X3))|~r1_xboole_0(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.43  cnf(c_0_28, plain, (k5_relat_1(k1_xboole_0,k5_relat_1(X1,X2))=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_19])])).
% 0.19/0.43  fof(c_0_29, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.19/0.43  fof(c_0_30, plain, ![X36, X37]:(~v1_relat_1(X36)|~v1_relat_1(X37)|v1_relat_1(k5_relat_1(X36,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.43  cnf(c_0_31, plain, (~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,X3),k5_relat_1(k1_xboole_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_12]), c_0_13])])).
% 0.19/0.43  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk5_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_33, plain, (k5_relat_1(k1_xboole_0,k1_xboole_0)=k5_relat_1(k1_xboole_0,X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_26]), c_0_19])])).
% 0.19/0.43  fof(c_0_34, negated_conjecture, (v1_relat_1(esk9_0)&(k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.19/0.43  cnf(c_0_35, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.43  cnf(c_0_36, plain, (X1!=k5_relat_1(X2,k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X5),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.43  cnf(c_0_37, plain, (k5_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_33])).
% 0.19/0.43  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.43  cnf(c_0_39, plain, (v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_25]), c_0_35])).
% 0.19/0.43  cnf(c_0_40, plain, (~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X2,k5_relat_1(k1_xboole_0,X1)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_35])).
% 0.19/0.43  cnf(c_0_41, negated_conjecture, (k5_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.43  cnf(c_0_42, plain, (v1_relat_1(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_19])])).
% 0.19/0.43  cnf(c_0_43, negated_conjecture, (~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_19])])).
% 0.19/0.43  cnf(c_0_44, negated_conjecture, (v1_relat_1(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.19/0.43  cnf(c_0_45, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.43  cnf(c_0_46, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_23]), c_0_44])).
% 0.19/0.43  cnf(c_0_47, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_38])]), c_0_26])).
% 0.19/0.43  cnf(c_0_48, negated_conjecture, (~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_26]), c_0_38])])).
% 0.19/0.43  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_38, c_0_48]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 50
% 0.19/0.43  # Proof object clause steps            : 33
% 0.19/0.43  # Proof object formula steps           : 17
% 0.19/0.43  # Proof object conjectures             : 12
% 0.19/0.43  # Proof object clause conjectures      : 9
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 11
% 0.19/0.43  # Proof object initial formulas used   : 8
% 0.19/0.43  # Proof object generating inferences   : 21
% 0.19/0.43  # Proof object simplifying inferences  : 26
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 8
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 17
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 17
% 0.19/0.43  # Processed clauses                    : 572
% 0.19/0.43  # ...of these trivial                  : 0
% 0.19/0.43  # ...subsumed                          : 415
% 0.19/0.43  # ...remaining for further processing  : 157
% 0.19/0.43  # Other redundant clauses eliminated   : 0
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 21
% 0.19/0.43  # Backward-rewritten                   : 4
% 0.19/0.43  # Generated clauses                    : 2776
% 0.19/0.43  # ...of the previous two non-trivial   : 2363
% 0.19/0.43  # Contextual simplify-reflections      : 29
% 0.19/0.43  # Paramodulations                      : 2755
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 18
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
% 0.19/0.43  # Current number of processed clauses  : 112
% 0.19/0.43  #    Positive orientable unit clauses  : 3
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 2
% 0.19/0.43  #    Non-unit-clauses                  : 107
% 0.19/0.43  # Current number of unprocessed clauses: 1695
% 0.19/0.43  # ...number of literals in the above   : 10409
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 45
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 7739
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 2465
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 399
% 0.19/0.43  # Unit Clause-clause subsumption calls : 104
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 2
% 0.19/0.43  # BW rewrite match successes           : 2
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 52761
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.089 s
% 0.19/0.43  # System time              : 0.003 s
% 0.19/0.43  # Total time               : 0.092 s
% 0.19/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

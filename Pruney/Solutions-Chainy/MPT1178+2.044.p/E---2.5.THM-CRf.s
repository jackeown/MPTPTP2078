%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:18 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 135 expanded)
%              Number of clauses        :   24 (  44 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 719 expanded)
%              Number of equality atoms :   10 (  82 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(existence_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ? [X3] : m2_orders_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t79_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_8,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X19,X18)
        | m2_orders_2(X19,X16,X17)
        | X18 != k4_orders_2(X16,X17)
        | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m2_orders_2(X20,X16,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_orders_2(X16,X17)
        | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X21),X21)
        | ~ m2_orders_2(esk2_3(X16,X17,X21),X16,X17)
        | X21 = k4_orders_2(X16,X17)
        | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) )
      & ( r2_hidden(esk2_3(X16,X17,X21),X21)
        | m2_orders_2(esk2_3(X16,X17,X21),X16,X17)
        | X21 = k4_orders_2(X16,X17)
        | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v3_orders_2(X16)
        | ~ v4_orders_2(X16)
        | ~ v5_orders_2(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | X4 != k4_orders_2(X2,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))
    & k3_tarski(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v3_orders_2(X23)
      | ~ v4_orders_2(X23)
      | ~ v5_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))
      | m2_orders_2(esk3_2(X23,X24),X23,X24) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k4_orders_2(X1,X3))
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk3_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | r1_tarski(X12,k3_tarski(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k4_orders_2(esk4_0,esk5_0))
    | ~ m2_orders_2(X1,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m2_orders_2(esk3_2(esk4_0,esk5_0),esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

fof(c_0_24,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v3_orders_2(X26)
      | ~ v4_orders_2(X26)
      | ~ v5_orders_2(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))
      | ~ m2_orders_2(X28,X26,X27)
      | r2_hidden(k1_funct_1(X27,u1_struct_0(X26)),X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

fof(c_0_25,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),k4_orders_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_2(esk4_0,esk5_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,u1_struct_0(esk4_0)),X1)
    | ~ m2_orders_2(X1,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

fof(c_0_33,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | ~ r1_tarski(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,esk3_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,u1_struct_0(esk4_0)),esk3_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_23])).

fof(c_0_36,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,u1_struct_0(esk4_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:46:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.12/0.37  # and selection function SelectNewComplexAHPNS.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.12/0.37  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.12/0.37  fof(existence_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>?[X3]:m2_orders_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 0.12/0.37  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.12/0.37  fof(t79_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.37  fof(c_0_8, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X19,X18)|m2_orders_2(X19,X16,X17)|X18!=k4_orders_2(X16,X17)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16)))&(~m2_orders_2(X20,X16,X17)|r2_hidden(X20,X18)|X18!=k4_orders_2(X16,X17)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16))))&((~r2_hidden(esk2_3(X16,X17,X21),X21)|~m2_orders_2(esk2_3(X16,X17,X21),X16,X17)|X21=k4_orders_2(X16,X17)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16)))&(r2_hidden(esk2_3(X16,X17,X21),X21)|m2_orders_2(esk2_3(X16,X17,X21),X16,X17)|X21=k4_orders_2(X16,X17)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.12/0.37  cnf(c_0_10, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))&k3_tarski(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X23, X24]:(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))|m2_orders_2(esk3_2(X23,X24),X23,X24)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).
% 0.12/0.37  cnf(c_0_13, plain, (v2_struct_0(X1)|r2_hidden(X2,k4_orders_2(X1,X3))|~m2_orders_2(X2,X1,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_20, plain, (v2_struct_0(X1)|m2_orders_2(esk3_2(X1,X2),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_21, plain, ![X12, X13]:(~r2_hidden(X12,X13)|r1_tarski(X12,k3_tarski(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,k4_orders_2(esk4_0,esk5_0))|~m2_orders_2(X1,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (m2_orders_2(esk3_2(esk4_0,esk5_0),esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  fof(c_0_24, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|(~m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))|(~m2_orders_2(X28,X26,X27)|r2_hidden(k1_funct_1(X27,u1_struct_0(X26)),X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).
% 0.12/0.37  fof(c_0_25, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  cnf(c_0_26, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),k4_orders_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (k3_tarski(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_29, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_2(esk4_0,esk5_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,u1_struct_0(esk4_0)),X1)|~m2_orders_2(X1,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  fof(c_0_33, plain, ![X14, X15]:(~r2_hidden(X14,X15)|~r1_tarski(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,esk3_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,u1_struct_0(esk4_0)),esk3_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_23])).
% 0.12/0.37  fof(c_0_36, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.37  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,u1_struct_0(esk4_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 41
% 0.12/0.37  # Proof object clause steps            : 24
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 19
% 0.12/0.37  # Proof object clause conjectures      : 16
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 14
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 9
% 0.12/0.37  # Proof object simplifying inferences  : 22
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 19
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 19
% 0.12/0.37  # Processed clauses                    : 39
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 39
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 32
% 0.12/0.37  # ...of the previous two non-trivial   : 27
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 30
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 37
% 0.12/0.37  #    Positive orientable unit clauses  : 14
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 20
% 0.12/0.37  # Current number of unprocessed clauses: 6
% 0.12/0.37  # ...number of literals in the above   : 21
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 0
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 222
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 58
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 24
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 39
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2301
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

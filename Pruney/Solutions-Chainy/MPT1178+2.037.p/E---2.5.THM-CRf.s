%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:17 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 131 expanded)
%              Number of clauses        :   23 (  43 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :  173 ( 717 expanded)
%              Number of equality atoms :   23 (  95 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X12,X11)
        | m2_orders_2(X12,X9,X10)
        | X11 != k4_orders_2(X9,X10)
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m2_orders_2(X13,X9,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_orders_2(X9,X10)
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ r2_hidden(esk2_3(X9,X10,X14),X14)
        | ~ m2_orders_2(esk2_3(X9,X10,X14),X9,X10)
        | X14 = k4_orders_2(X9,X10)
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk2_3(X9,X10,X14),X14)
        | m2_orders_2(esk2_3(X9,X10,X14),X9,X10)
        | X14 = k4_orders_2(X9,X10)
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_9,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v3_orders_2(X19)
      | ~ v4_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(X19)))
      | ~ m2_orders_2(X21,X19,X20)
      | r2_hidden(k1_funct_1(X20,u1_struct_0(X19)),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))
    & k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ v3_orders_2(X16)
      | ~ v4_orders_2(X16)
      | ~ v5_orders_2(X16)
      | ~ l1_orders_2(X16)
      | ~ m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))
      | m2_orders_2(esk3_2(X16,X17),X16,X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).

cnf(c_0_12,plain,
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

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(esk3_2(X1,X2),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X22,X23,X24] :
      ( ( X23 = k1_xboole_0
        | ~ r2_hidden(X23,X22)
        | k3_tarski(X22) != k1_xboole_0 )
      & ( esk4_1(X24) != k1_xboole_0
        | k3_tarski(X24) = k1_xboole_0 )
      & ( r2_hidden(esk4_1(X24),X24)
        | k3_tarski(X24) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k4_orders_2(X1,X3))
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_23,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,u1_struct_0(esk5_0)),X1)
    | ~ m2_orders_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m2_orders_2(esk3_2(esk5_0,esk6_0),esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k4_orders_2(esk5_0,esk6_0))
    | ~ m2_orders_2(X1,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,u1_struct_0(esk5_0)),esk3_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k4_orders_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k4_orders_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk3_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk3_2(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.13/0.37  # and selection function SelectNewComplexAHPNS.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.13/0.37  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.13/0.37  fof(t79_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 0.13/0.37  fof(existence_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>?[X3]:m2_orders_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 0.13/0.37  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 0.13/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.13/0.37  fof(c_0_8, plain, ![X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X12,X11)|m2_orders_2(X12,X9,X10)|X11!=k4_orders_2(X9,X10)|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)))&(~m2_orders_2(X13,X9,X10)|r2_hidden(X13,X11)|X11!=k4_orders_2(X9,X10)|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9))))&((~r2_hidden(esk2_3(X9,X10,X14),X14)|~m2_orders_2(esk2_3(X9,X10,X14),X9,X10)|X14=k4_orders_2(X9,X10)|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)))&(r2_hidden(esk2_3(X9,X10,X14),X14)|m2_orders_2(esk2_3(X9,X10,X14),X9,X10)|X14=k4_orders_2(X9,X10)|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.13/0.37  fof(c_0_9, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|(~m1_orders_1(X20,k1_orders_1(u1_struct_0(X19)))|(~m2_orders_2(X21,X19,X20)|r2_hidden(k1_funct_1(X20,u1_struct_0(X19)),X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).
% 0.13/0.37  fof(c_0_10, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&(m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))&k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.13/0.37  fof(c_0_11, plain, ![X16, X17]:(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16)|~m1_orders_1(X17,k1_orders_1(u1_struct_0(X16)))|m2_orders_2(esk3_2(X16,X17),X16,X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m2_orders_2])])])])).
% 0.13/0.37  cnf(c_0_12, plain, (r2_hidden(X1,X4)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|X4!=k4_orders_2(X2,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_20, plain, (v2_struct_0(X1)|m2_orders_2(esk3_2(X1,X2),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  fof(c_0_21, plain, ![X22, X23, X24]:((X23=k1_xboole_0|~r2_hidden(X23,X22)|k3_tarski(X22)!=k1_xboole_0)&((esk4_1(X24)!=k1_xboole_0|k3_tarski(X24)=k1_xboole_0)&(r2_hidden(esk4_1(X24),X24)|k3_tarski(X24)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.13/0.37  cnf(c_0_22, plain, (v2_struct_0(X1)|r2_hidden(X2,k4_orders_2(X1,X3))|~m2_orders_2(X2,X1,X3)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_23, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,u1_struct_0(esk5_0)),X1)|~m2_orders_2(X1,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (m2_orders_2(esk3_2(esk5_0,esk6_0),esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.37  cnf(c_0_26, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,k4_orders_2(esk5_0,esk6_0))|~m2_orders_2(X1,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.37  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,u1_struct_0(esk5_0)),esk3_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (X1=k1_xboole_0|~r2_hidden(X1,k4_orders_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk6_0),k4_orders_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk3_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (esk3_2(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.37  cnf(c_0_35, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 37
% 0.13/0.37  # Proof object clause steps            : 23
% 0.13/0.37  # Proof object formula steps           : 14
% 0.13/0.37  # Proof object conjectures             : 19
% 0.13/0.37  # Proof object clause conjectures      : 16
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 7
% 0.13/0.37  # Proof object generating inferences   : 8
% 0.13/0.37  # Proof object simplifying inferences  : 22
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 7
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 19
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 19
% 0.13/0.37  # Processed clauses                    : 37
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 37
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 4
% 0.13/0.37  # Generated clauses                    : 31
% 0.13/0.37  # ...of the previous two non-trivial   : 26
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 27
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 2
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 29
% 0.13/0.37  #    Positive orientable unit clauses  : 9
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 18
% 0.13/0.37  # Current number of unprocessed clauses: 7
% 0.13/0.37  # ...number of literals in the above   : 22
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 6
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 142
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 62
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 33
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 37
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2211
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:13 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   40 (  73 expanded)
%              Number of clauses        :   22 (  28 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  177 ( 359 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ~ r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(t29_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_9,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r2_waybel_0(X30,X31,X32)
        | ~ r1_waybel_0(X30,X31,k6_subset_1(u1_struct_0(X30),X32))
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30) )
      & ( r1_waybel_0(X30,X31,k6_subset_1(u1_struct_0(X30),X32))
        | r2_waybel_0(X30,X31,X32)
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_10,plain,(
    ! [X20,X21] : k6_subset_1(X20,X21) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk2_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk2_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_13,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_16,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X22,X23,X24,X25,X27,X29] :
      ( ( m1_subset_1(esk4_4(X22,X23,X24,X25),u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ r2_waybel_0(X22,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( r1_orders_2(X23,X25,esk4_4(X22,X23,X24,X25))
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ r2_waybel_0(X22,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( r2_hidden(k2_waybel_0(X22,X23,esk4_4(X22,X23,X24,X25)),X24)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ r2_waybel_0(X22,X23,X24)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( m1_subset_1(esk5_3(X22,X23,X27),u1_struct_0(X23))
        | r2_waybel_0(X22,X23,X27)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X23))
        | ~ r1_orders_2(X23,esk5_3(X22,X23,X27),X29)
        | ~ r2_hidden(k2_waybel_0(X22,X23,X29),X27)
        | r2_waybel_0(X22,X23,X27)
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t29_yellow_6])).

cnf(c_0_20,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_24,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X18] : m1_subset_1(esk3_1(X18),X18) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & v4_orders_2(esk7_0)
    & v7_waybel_0(esk7_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_27,plain,
    ( r1_waybel_0(X1,X2,u1_struct_0(X1))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X2,X1,X3)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_waybel_0(X1,X2,u1_struct_0(X1))
    | r2_waybel_0(X1,X2,k1_xboole_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_33]),c_0_34]),c_0_23])]),c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n011.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 11:03:41 EST 2020
% 0.10/0.25  % CPUTime    : 
% 0.10/0.25  # Version: 2.5pre002
% 0.10/0.26  # No SInE strategy applied
% 0.10/0.26  # Trying AutoSched0 for 299 seconds
% 0.10/0.27  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.10/0.27  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.10/0.27  #
% 0.10/0.27  # Preprocessing time       : 0.013 s
% 0.10/0.27  
% 0.10/0.27  # Proof found!
% 0.10/0.27  # SZS status Theorem
% 0.10/0.27  # SZS output start CNFRefutation
% 0.10/0.27  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.10/0.27  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.10/0.27  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.10/0.27  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.10/0.27  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.10/0.27  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.10/0.27  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.10/0.27  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.10/0.27  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.10/0.27  fof(c_0_9, plain, ![X30, X31, X32]:((~r2_waybel_0(X30,X31,X32)|~r1_waybel_0(X30,X31,k6_subset_1(u1_struct_0(X30),X32))|(v2_struct_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~l1_struct_0(X30)))&(r1_waybel_0(X30,X31,k6_subset_1(u1_struct_0(X30),X32))|r2_waybel_0(X30,X31,X32)|(v2_struct_0(X31)|~l1_waybel_0(X31,X30))|(v2_struct_0(X30)|~l1_struct_0(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.10/0.27  fof(c_0_10, plain, ![X20, X21]:k6_subset_1(X20,X21)=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.10/0.27  fof(c_0_11, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.10/0.27  fof(c_0_12, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk2_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk2_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.10/0.27  cnf(c_0_13, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.10/0.27  cnf(c_0_14, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.10/0.27  fof(c_0_15, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.10/0.27  cnf(c_0_16, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.10/0.27  cnf(c_0_17, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.27  fof(c_0_18, plain, ![X22, X23, X24, X25, X27, X29]:((((m1_subset_1(esk4_4(X22,X23,X24,X25),u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X23))|~r2_waybel_0(X22,X23,X24)|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22)))&(r1_orders_2(X23,X25,esk4_4(X22,X23,X24,X25))|~m1_subset_1(X25,u1_struct_0(X23))|~r2_waybel_0(X22,X23,X24)|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))&(r2_hidden(k2_waybel_0(X22,X23,esk4_4(X22,X23,X24,X25)),X24)|~m1_subset_1(X25,u1_struct_0(X23))|~r2_waybel_0(X22,X23,X24)|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))&((m1_subset_1(esk5_3(X22,X23,X27),u1_struct_0(X23))|r2_waybel_0(X22,X23,X27)|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22)))&(~m1_subset_1(X29,u1_struct_0(X23))|~r1_orders_2(X23,esk5_3(X22,X23,X27),X29)|~r2_hidden(k2_waybel_0(X22,X23,X29),X27)|r2_waybel_0(X22,X23,X27)|(v2_struct_0(X23)|~l1_waybel_0(X23,X22))|(v2_struct_0(X22)|~l1_struct_0(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.10/0.27  fof(c_0_19, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.10/0.27  cnf(c_0_20, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.10/0.27  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.10/0.27  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.10/0.27  cnf(c_0_23, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.10/0.27  cnf(c_0_24, plain, (r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.10/0.27  fof(c_0_25, plain, ![X18]:m1_subset_1(esk3_1(X18),X18), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.10/0.27  fof(c_0_26, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&((((~v2_struct_0(esk7_0)&v4_orders_2(esk7_0))&v7_waybel_0(esk7_0))&l1_waybel_0(esk7_0,esk6_0))&~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.10/0.27  cnf(c_0_27, plain, (r1_waybel_0(X1,X2,u1_struct_0(X1))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.10/0.27  cnf(c_0_28, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.10/0.27  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X2,X1,X3)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X1))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_16, c_0_24])).
% 0.10/0.27  cnf(c_0_30, plain, (m1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.10/0.27  cnf(c_0_31, negated_conjecture, (~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.10/0.27  cnf(c_0_32, plain, (r1_waybel_0(X1,X2,u1_struct_0(X1))|r2_waybel_0(X1,X2,k1_xboole_0)|v2_struct_0(X1)|v2_struct_0(X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.10/0.27  cnf(c_0_33, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.10/0.27  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.10/0.27  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.10/0.27  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.10/0.27  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.10/0.27  cnf(c_0_38, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])]), c_0_35]), c_0_36])).
% 0.10/0.27  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_33]), c_0_34]), c_0_23])]), c_0_35]), c_0_36]), ['proof']).
% 0.10/0.27  # SZS output end CNFRefutation
% 0.10/0.27  # Proof object total steps             : 40
% 0.10/0.27  # Proof object clause steps            : 22
% 0.10/0.27  # Proof object formula steps           : 18
% 0.10/0.27  # Proof object conjectures             : 10
% 0.10/0.27  # Proof object clause conjectures      : 7
% 0.10/0.27  # Proof object formula conjectures     : 3
% 0.10/0.27  # Proof object initial clauses used    : 13
% 0.10/0.27  # Proof object initial formulas used   : 9
% 0.10/0.27  # Proof object generating inferences   : 8
% 0.10/0.27  # Proof object simplifying inferences  : 12
% 0.10/0.27  # Training examples: 0 positive, 0 negative
% 0.10/0.27  # Parsed axioms                        : 9
% 0.10/0.27  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.27  # Initial clauses                      : 24
% 0.10/0.27  # Removed in clause preprocessing      : 1
% 0.10/0.27  # Initial clauses in saturation        : 23
% 0.10/0.27  # Processed clauses                    : 36
% 0.10/0.27  # ...of these trivial                  : 0
% 0.10/0.27  # ...subsumed                          : 1
% 0.10/0.27  # ...remaining for further processing  : 35
% 0.10/0.27  # Other redundant clauses eliminated   : 0
% 0.10/0.27  # Clauses deleted for lack of memory   : 0
% 0.10/0.27  # Backward-subsumed                    : 1
% 0.10/0.27  # Backward-rewritten                   : 0
% 0.10/0.27  # Generated clauses                    : 25
% 0.10/0.27  # ...of the previous two non-trivial   : 17
% 0.10/0.27  # Contextual simplify-reflections      : 0
% 0.10/0.27  # Paramodulations                      : 25
% 0.10/0.27  # Factorizations                       : 0
% 0.10/0.27  # Equation resolutions                 : 0
% 0.10/0.27  # Propositional unsat checks           : 0
% 0.10/0.27  #    Propositional check models        : 0
% 0.10/0.27  #    Propositional check unsatisfiable : 0
% 0.10/0.27  #    Propositional clauses             : 0
% 0.10/0.27  #    Propositional clauses after purity: 0
% 0.10/0.27  #    Propositional unsat core size     : 0
% 0.10/0.27  #    Propositional preprocessing time  : 0.000
% 0.10/0.27  #    Propositional encoding time       : 0.000
% 0.10/0.27  #    Propositional solver time         : 0.000
% 0.10/0.27  #    Success case prop preproc time    : 0.000
% 0.10/0.27  #    Success case prop encoding time   : 0.000
% 0.10/0.27  #    Success case prop solver time     : 0.000
% 0.10/0.27  # Current number of processed clauses  : 34
% 0.10/0.27  #    Positive orientable unit clauses  : 9
% 0.10/0.27  #    Positive unorientable unit clauses: 0
% 0.10/0.27  #    Negative unit clauses             : 3
% 0.10/0.27  #    Non-unit-clauses                  : 22
% 0.10/0.27  # Current number of unprocessed clauses: 4
% 0.10/0.27  # ...number of literals in the above   : 40
% 0.10/0.27  # Current number of archived formulas  : 0
% 0.10/0.27  # Current number of archived clauses   : 2
% 0.10/0.27  # Clause-clause subsumption calls (NU) : 332
% 0.10/0.27  # Rec. Clause-clause subsumption calls : 15
% 0.10/0.27  # Non-unit clause-clause subsumptions  : 2
% 0.10/0.27  # Unit Clause-clause subsumption calls : 10
% 0.10/0.27  # Rewrite failures with RHS unbound    : 0
% 0.10/0.27  # BW rewrite match attempts            : 0
% 0.10/0.27  # BW rewrite match successes           : 0
% 0.10/0.27  # Condensation attempts                : 0
% 0.10/0.27  # Condensation successes               : 0
% 0.10/0.27  # Termbank termtop insertions          : 2228
% 0.10/0.27  
% 0.10/0.27  # -------------------------------------------------
% 0.10/0.27  # User time                : 0.015 s
% 0.10/0.27  # System time              : 0.001 s
% 0.10/0.27  # Total time               : 0.016 s
% 0.10/0.27  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

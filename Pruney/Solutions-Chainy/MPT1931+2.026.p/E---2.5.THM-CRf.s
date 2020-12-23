%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 104 expanded)
%              Number of clauses        :   28 (  39 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  192 ( 467 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   35 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ( r1_tarski(X3,X4)
             => ( ( r1_waybel_0(X1,X2,X3)
                 => r1_waybel_0(X1,X2,X4) )
                & ( r2_waybel_0(X1,X2,X3)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

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

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_11,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r2_waybel_0(X33,X34,X35)
        | ~ r1_waybel_0(X33,X34,k6_subset_1(u1_struct_0(X33),X35))
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33) )
      & ( r1_waybel_0(X33,X34,k6_subset_1(u1_struct_0(X33),X35))
        | r2_waybel_0(X33,X34,X35)
        | v2_struct_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_12,plain,(
    ! [X16,X17] : k6_subset_1(X16,X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_13,negated_conjecture,(
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

cnf(c_0_14,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & v4_orders_2(esk7_0)
    & v7_waybel_0(esk7_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_23,plain,(
    ! [X36,X37,X38,X39] :
      ( ( ~ r1_waybel_0(X36,X37,X38)
        | r1_waybel_0(X36,X37,X39)
        | ~ r1_tarski(X38,X39)
        | v2_struct_0(X37)
        | ~ l1_waybel_0(X37,X36)
        | v2_struct_0(X36)
        | ~ l1_struct_0(X36) )
      & ( ~ r2_waybel_0(X36,X37,X38)
        | r2_waybel_0(X36,X37,X39)
        | ~ r1_tarski(X38,X39)
        | v2_struct_0(X37)
        | ~ l1_waybel_0(X37,X36)
        | v2_struct_0(X36)
        | ~ l1_struct_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).

cnf(c_0_24,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,k4_xboole_0(u1_struct_0(esk6_0),X1))
    | r2_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_28,plain,(
    ! [X18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_29,plain,
    ( r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ r1_tarski(X3,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_31,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1)
    | r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_38,plain,(
    v1_xboole_0(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

fof(c_0_39,plain,(
    ! [X25,X26,X27,X28,X30,X32] :
      ( ( m1_subset_1(esk4_4(X25,X26,X27,X28),u1_struct_0(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ r2_waybel_0(X25,X26,X27)
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) )
      & ( r1_orders_2(X26,X28,esk4_4(X25,X26,X27,X28))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ r2_waybel_0(X25,X26,X27)
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) )
      & ( r2_hidden(k2_waybel_0(X25,X26,esk4_4(X25,X26,X27,X28)),X27)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ r2_waybel_0(X25,X26,X27)
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) )
      & ( m1_subset_1(esk5_3(X25,X26,X30),u1_struct_0(X26))
        | r2_waybel_0(X25,X26,X30)
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X26))
        | ~ r1_orders_2(X26,esk5_3(X25,X26,X30),X32)
        | ~ r2_hidden(k2_waybel_0(X25,X26,X32),X30)
        | r2_waybel_0(X25,X26,X30)
        | v2_struct_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_struct_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_42,plain,(
    ! [X14] : m1_subset_1(esk3_1(X14),X14) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_43,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk3_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,X1,esk3_1(u1_struct_0(esk7_0)))),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_41,c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:05:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.13/0.37  # and selection function SelectCQArNTNpEqFirst.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.13/0.37  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.13/0.37  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.13/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.37  fof(t8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:(r1_tarski(X3,X4)=>((r1_waybel_0(X1,X2,X3)=>r1_waybel_0(X1,X2,X4))&(r2_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 0.13/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.13/0.37  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.13/0.37  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.13/0.37  fof(c_0_11, plain, ![X33, X34, X35]:((~r2_waybel_0(X33,X34,X35)|~r1_waybel_0(X33,X34,k6_subset_1(u1_struct_0(X33),X35))|(v2_struct_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~l1_struct_0(X33)))&(r1_waybel_0(X33,X34,k6_subset_1(u1_struct_0(X33),X35))|r2_waybel_0(X33,X34,X35)|(v2_struct_0(X34)|~l1_waybel_0(X34,X33))|(v2_struct_0(X33)|~l1_struct_0(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.13/0.37  fof(c_0_12, plain, ![X16, X17]:k6_subset_1(X16,X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.13/0.37  cnf(c_0_14, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_15, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_16, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&((((~v2_struct_0(esk7_0)&v4_orders_2(esk7_0))&v7_waybel_0(esk7_0))&l1_waybel_0(esk7_0,esk6_0))&~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.37  cnf(c_0_17, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  fof(c_0_22, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.37  fof(c_0_23, plain, ![X36, X37, X38, X39]:((~r1_waybel_0(X36,X37,X38)|r1_waybel_0(X36,X37,X39)|~r1_tarski(X38,X39)|(v2_struct_0(X37)|~l1_waybel_0(X37,X36))|(v2_struct_0(X36)|~l1_struct_0(X36)))&(~r2_waybel_0(X36,X37,X38)|r2_waybel_0(X36,X37,X39)|~r1_tarski(X38,X39)|(v2_struct_0(X37)|~l1_waybel_0(X37,X36))|(v2_struct_0(X36)|~l1_struct_0(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r1_waybel_0(esk6_0,esk7_0,k4_xboole_0(u1_struct_0(esk6_0),X1))|r2_waybel_0(esk6_0,esk7_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 0.13/0.37  cnf(c_0_25, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  fof(c_0_27, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|~v1_xboole_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.37  fof(c_0_28, plain, ![X18]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.37  cnf(c_0_29, plain, (r2_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_0(X1,X2,X3)|~r1_tarski(X3,X4)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.13/0.37  fof(c_0_31, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_33, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)|~r1_tarski(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 0.13/0.37  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_36, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)|r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.37  fof(c_0_38, plain, v1_xboole_0(esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.13/0.37  fof(c_0_39, plain, ![X25, X26, X27, X28, X30, X32]:((((m1_subset_1(esk4_4(X25,X26,X27,X28),u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26))|~r2_waybel_0(X25,X26,X27)|(v2_struct_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~l1_struct_0(X25)))&(r1_orders_2(X26,X28,esk4_4(X25,X26,X27,X28))|~m1_subset_1(X28,u1_struct_0(X26))|~r2_waybel_0(X25,X26,X27)|(v2_struct_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~l1_struct_0(X25))))&(r2_hidden(k2_waybel_0(X25,X26,esk4_4(X25,X26,X27,X28)),X27)|~m1_subset_1(X28,u1_struct_0(X26))|~r2_waybel_0(X25,X26,X27)|(v2_struct_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~l1_struct_0(X25))))&((m1_subset_1(esk5_3(X25,X26,X30),u1_struct_0(X26))|r2_waybel_0(X25,X26,X30)|(v2_struct_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~l1_struct_0(X25)))&(~m1_subset_1(X32,u1_struct_0(X26))|~r1_orders_2(X26,esk5_3(X25,X26,X30),X32)|~r2_hidden(k2_waybel_0(X25,X26,X32),X30)|r2_waybel_0(X25,X26,X30)|(v2_struct_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~l1_struct_0(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.37  cnf(c_0_41, plain, (v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.37  fof(c_0_42, plain, ![X14]:m1_subset_1(esk3_1(X14),X14), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.13/0.37  cnf(c_0_43, plain, (r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.37  cnf(c_0_45, plain, (m1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,X1,X2)),X1)|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 0.13/0.37  cnf(c_0_47, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,esk3_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_32, c_0_45])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,X1,esk3_1(u1_struct_0(esk7_0)))),X1)), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.37  cnf(c_0_50, plain, ($false), inference(sr,[status(thm)],[c_0_41, c_0_49]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 51
% 0.13/0.37  # Proof object clause steps            : 28
% 0.13/0.37  # Proof object formula steps           : 23
% 0.13/0.37  # Proof object conjectures             : 17
% 0.13/0.37  # Proof object clause conjectures      : 14
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 15
% 0.13/0.37  # Proof object initial formulas used   : 11
% 0.13/0.37  # Proof object generating inferences   : 11
% 0.13/0.37  # Proof object simplifying inferences  : 17
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 12
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 26
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 25
% 0.13/0.37  # Processed clauses                    : 75
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 75
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 5
% 0.13/0.37  # Generated clauses                    : 45
% 0.13/0.37  # ...of the previous two non-trivial   : 41
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 44
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
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
% 0.13/0.37  # Current number of processed clauses  : 43
% 0.13/0.37  #    Positive orientable unit clauses  : 16
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 4
% 0.13/0.37  #    Non-unit-clauses                  : 23
% 0.13/0.37  # Current number of unprocessed clauses: 14
% 0.13/0.37  # ...number of literals in the above   : 15
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 33
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 507
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 33
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 28
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 19
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3493
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.033 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:21:15 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 104 expanded)
%              Number of clauses        :   29 (  39 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 473 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_11,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r2_waybel_0(X34,X35,X36)
        | ~ r1_waybel_0(X34,X35,k6_subset_1(u1_struct_0(X34),X36))
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) )
      & ( r1_waybel_0(X34,X35,k6_subset_1(u1_struct_0(X34),X36))
        | r2_waybel_0(X34,X35,X36)
        | v2_struct_0(X35)
        | ~ l1_waybel_0(X35,X34)
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_12,plain,(
    ! [X17,X18] : k6_subset_1(X17,X18) = k4_xboole_0(X17,X18) ),
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
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_23,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ r1_waybel_0(X37,X38,X39)
        | r1_waybel_0(X37,X38,X40)
        | ~ r1_tarski(X39,X40)
        | v2_struct_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | v2_struct_0(X37)
        | ~ l1_struct_0(X37) )
      & ( ~ r2_waybel_0(X37,X38,X39)
        | r2_waybel_0(X37,X38,X40)
        | ~ r1_tarski(X39,X40)
        | v2_struct_0(X38)
        | ~ l1_waybel_0(X38,X37)
        | v2_struct_0(X37)
        | ~ l1_struct_0(X37) ) ) ),
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
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | ~ v1_xboole_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_28,plain,(
    ! [X19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)) ),
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
    ! [X15] :
      ( m1_subset_1(esk3_1(X15),k1_zfmisc_1(X15))
      & v1_xboole_0(esk3_1(X15)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

fof(c_0_39,plain,(
    ! [X26,X27,X28,X29,X31,X33] :
      ( ( m1_subset_1(esk4_4(X26,X27,X28,X29),u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ r2_waybel_0(X26,X27,X28)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( r1_orders_2(X27,X29,esk4_4(X26,X27,X28,X29))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ r2_waybel_0(X26,X27,X28)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( r2_hidden(k2_waybel_0(X26,X27,esk4_4(X26,X27,X28,X29)),X28)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ r2_waybel_0(X26,X27,X28)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( m1_subset_1(esk5_3(X26,X27,X31),u1_struct_0(X27))
        | r2_waybel_0(X26,X27,X31)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X27))
        | ~ r1_orders_2(X27,esk5_3(X26,X27,X31),X33)
        | ~ r2_hidden(k2_waybel_0(X26,X27,X33),X31)
        | r2_waybel_0(X26,X27,X31)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( v1_xboole_0(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_44,plain,(
    ! [X13] : m1_subset_1(esk2_1(X13),X13) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk3_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,X1,esk2_1(u1_struct_0(esk7_0)))),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_41,c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.13/0.38  # and selection function SelectCQArNTNpEqFirst.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.13/0.38  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.13/0.38  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.13/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.38  fof(t8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:(r1_tarski(X3,X4)=>((r1_waybel_0(X1,X2,X3)=>r1_waybel_0(X1,X2,X4))&(r2_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_0)).
% 0.13/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.13/0.38  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.13/0.38  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.13/0.38  fof(c_0_11, plain, ![X34, X35, X36]:((~r2_waybel_0(X34,X35,X36)|~r1_waybel_0(X34,X35,k6_subset_1(u1_struct_0(X34),X36))|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~l1_struct_0(X34)))&(r1_waybel_0(X34,X35,k6_subset_1(u1_struct_0(X34),X36))|r2_waybel_0(X34,X35,X36)|(v2_struct_0(X35)|~l1_waybel_0(X35,X34))|(v2_struct_0(X34)|~l1_struct_0(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X17, X18]:k6_subset_1(X17,X18)=k4_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.13/0.38  cnf(c_0_14, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&((((~v2_struct_0(esk7_0)&v4_orders_2(esk7_0))&v7_waybel_0(esk7_0))&l1_waybel_0(esk7_0,esk6_0))&~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.38  cnf(c_0_17, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_22, plain, ![X12]:k4_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.38  fof(c_0_23, plain, ![X37, X38, X39, X40]:((~r1_waybel_0(X37,X38,X39)|r1_waybel_0(X37,X38,X40)|~r1_tarski(X39,X40)|(v2_struct_0(X38)|~l1_waybel_0(X38,X37))|(v2_struct_0(X37)|~l1_struct_0(X37)))&(~r2_waybel_0(X37,X38,X39)|r2_waybel_0(X37,X38,X40)|~r1_tarski(X39,X40)|(v2_struct_0(X38)|~l1_waybel_0(X38,X37))|(v2_struct_0(X37)|~l1_struct_0(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (r1_waybel_0(esk6_0,esk7_0,k4_xboole_0(u1_struct_0(esk6_0),X1))|r2_waybel_0(esk6_0,esk7_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 0.13/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_27, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|~v1_xboole_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.38  fof(c_0_28, plain, ![X19]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.38  cnf(c_0_29, plain, (r2_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_0(X1,X2,X3)|~r1_tarski(X3,X4)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.13/0.38  fof(c_0_31, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_33, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)|~r1_tarski(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 0.13/0.38  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_36, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)|r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  fof(c_0_38, plain, ![X15]:(m1_subset_1(esk3_1(X15),k1_zfmisc_1(X15))&v1_xboole_0(esk3_1(X15))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.13/0.38  fof(c_0_39, plain, ![X26, X27, X28, X29, X31, X33]:((((m1_subset_1(esk4_4(X26,X27,X28,X29),u1_struct_0(X27))|~m1_subset_1(X29,u1_struct_0(X27))|~r2_waybel_0(X26,X27,X28)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26)))&(r1_orders_2(X27,X29,esk4_4(X26,X27,X28,X29))|~m1_subset_1(X29,u1_struct_0(X27))|~r2_waybel_0(X26,X27,X28)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26))))&(r2_hidden(k2_waybel_0(X26,X27,esk4_4(X26,X27,X28,X29)),X28)|~m1_subset_1(X29,u1_struct_0(X27))|~r2_waybel_0(X26,X27,X28)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26))))&((m1_subset_1(esk5_3(X26,X27,X31),u1_struct_0(X27))|r2_waybel_0(X26,X27,X31)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26)))&(~m1_subset_1(X33,u1_struct_0(X27))|~r1_orders_2(X27,esk5_3(X26,X27,X31),X33)|~r2_hidden(k2_waybel_0(X26,X27,X33),X31)|r2_waybel_0(X26,X27,X31)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~l1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_41, plain, (v1_xboole_0(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_42, plain, (r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.38  fof(c_0_44, plain, ![X13]:m1_subset_1(esk2_1(X13),X13), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.13/0.38  cnf(c_0_45, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,X1,X2)),X1)|~m1_subset_1(X2,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 0.13/0.38  cnf(c_0_47, plain, (m1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_48, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,esk3_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_45])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,X1,esk2_1(u1_struct_0(esk7_0)))),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_51, plain, ($false), inference(sr,[status(thm)],[c_0_41, c_0_50]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 52
% 0.13/0.38  # Proof object clause steps            : 29
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 16
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 17
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 27
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 26
% 0.13/0.38  # Processed clauses                    : 90
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 4
% 0.13/0.38  # ...remaining for further processing  : 86
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 12
% 0.13/0.38  # Backward-rewritten                   : 7
% 0.13/0.38  # Generated clauses                    : 70
% 0.13/0.38  # ...of the previous two non-trivial   : 66
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 69
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 40
% 0.13/0.38  #    Positive orientable unit clauses  : 13
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 23
% 0.13/0.38  # Current number of unprocessed clauses: 21
% 0.13/0.38  # ...number of literals in the above   : 41
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 47
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 397
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 88
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.13/0.38  # Unit Clause-clause subsumption calls : 20
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 8
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4014
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

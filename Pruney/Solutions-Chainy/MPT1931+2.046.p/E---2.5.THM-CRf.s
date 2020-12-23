%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:17 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 172 expanded)
%              Number of clauses        :   28 (  68 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 751 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   35 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

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

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

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

fof(c_0_10,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_11,plain,(
    ! [X20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k4_xboole_0(X12,X13) = X12 )
      & ( k4_xboole_0(X12,X13) != X12
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_13,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r2_waybel_0(X35,X36,X37)
        | ~ r1_waybel_0(X35,X36,k6_subset_1(u1_struct_0(X35),X37))
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) )
      & ( r1_waybel_0(X35,X36,k6_subset_1(u1_struct_0(X35),X37))
        | r2_waybel_0(X35,X36,X37)
        | v2_struct_0(X36)
        | ~ l1_waybel_0(X36,X35)
        | v2_struct_0(X35)
        | ~ l1_struct_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_15,plain,(
    ! [X18,X19] : k6_subset_1(X18,X19) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_16,negated_conjecture,(
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

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_struct_0(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & v4_orders_2(esk7_0)
    & v7_waybel_0(esk7_0)
    & l1_waybel_0(esk7_0,esk6_0)
    & ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,plain,(
    ! [X16] :
      ( m1_subset_1(esk3_1(X16),k1_zfmisc_1(X16))
      & v1_xboole_0(esk3_1(X16)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( l1_waybel_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( v1_xboole_0(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X27,X28,X29,X30,X32,X34] :
      ( ( m1_subset_1(esk4_4(X27,X28,X29,X30),u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ r2_waybel_0(X27,X28,X29)
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) )
      & ( r1_orders_2(X28,X30,esk4_4(X27,X28,X29,X30))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ r2_waybel_0(X27,X28,X29)
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) )
      & ( r2_hidden(k2_waybel_0(X27,X28,esk4_4(X27,X28,X29,X30)),X29)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ r2_waybel_0(X27,X28,X29)
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) )
      & ( m1_subset_1(esk5_3(X27,X28,X32),u1_struct_0(X28))
        | r2_waybel_0(X27,X28,X32)
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) )
      & ( ~ m1_subset_1(X34,u1_struct_0(X28))
        | ~ r1_orders_2(X28,esk5_3(X27,X28,X32),X34)
        | ~ r2_hidden(k2_waybel_0(X27,X28,X34),X32)
        | r2_waybel_0(X27,X28,X32)
        | v2_struct_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ l1_struct_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_waybel_0(esk6_0,esk7_0,k4_xboole_0(u1_struct_0(esk6_0),X1))
    | r2_waybel_0(esk6_0,esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_waybel_0(esk6_0,esk7_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

fof(c_0_41,plain,(
    ! [X14] : m1_subset_1(esk2_1(X14),X14) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,k1_xboole_0,X1)),k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,k1_xboole_0,esk2_1(u1_struct_0(esk7_0)))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.19/0.39  # and selection function SelectCQArNTNpEqFirst.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.037 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.39  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.39  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.19/0.39  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.39  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.19/0.39  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.19/0.39  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.19/0.39  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.19/0.39  fof(c_0_10, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|~v1_xboole_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.39  fof(c_0_11, plain, ![X20]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.39  fof(c_0_12, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k4_xboole_0(X12,X13)=X12)&(k4_xboole_0(X12,X13)!=X12|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.39  fof(c_0_13, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.39  fof(c_0_14, plain, ![X35, X36, X37]:((~r2_waybel_0(X35,X36,X37)|~r1_waybel_0(X35,X36,k6_subset_1(u1_struct_0(X35),X37))|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35)))&(r1_waybel_0(X35,X36,k6_subset_1(u1_struct_0(X35),X37))|r2_waybel_0(X35,X36,X37)|(v2_struct_0(X36)|~l1_waybel_0(X36,X35))|(v2_struct_0(X35)|~l1_struct_0(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.19/0.39  fof(c_0_15, plain, ![X18, X19]:k6_subset_1(X18,X19)=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.19/0.39  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_18, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_21, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_22, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  fof(c_0_23, negated_conjecture, ((~v2_struct_0(esk6_0)&l1_struct_0(esk6_0))&((((~v2_struct_0(esk7_0)&v4_orders_2(esk7_0))&v7_waybel_0(esk7_0))&l1_waybel_0(esk7_0,esk6_0))&~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.19/0.39  cnf(c_0_24, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.39  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.39  fof(c_0_26, plain, ![X16]:(m1_subset_1(esk3_1(X16),k1_zfmisc_1(X16))&v1_xboole_0(esk3_1(X16))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.19/0.39  cnf(c_0_27, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (l1_waybel_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (l1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.39  cnf(c_0_33, plain, (v1_xboole_0(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  fof(c_0_34, plain, ![X27, X28, X29, X30, X32, X34]:((((m1_subset_1(esk4_4(X27,X28,X29,X30),u1_struct_0(X28))|~m1_subset_1(X30,u1_struct_0(X28))|~r2_waybel_0(X27,X28,X29)|(v2_struct_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~l1_struct_0(X27)))&(r1_orders_2(X28,X30,esk4_4(X27,X28,X29,X30))|~m1_subset_1(X30,u1_struct_0(X28))|~r2_waybel_0(X27,X28,X29)|(v2_struct_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~l1_struct_0(X27))))&(r2_hidden(k2_waybel_0(X27,X28,esk4_4(X27,X28,X29,X30)),X29)|~m1_subset_1(X30,u1_struct_0(X28))|~r2_waybel_0(X27,X28,X29)|(v2_struct_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~l1_struct_0(X27))))&((m1_subset_1(esk5_3(X27,X28,X32),u1_struct_0(X28))|r2_waybel_0(X27,X28,X32)|(v2_struct_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~l1_struct_0(X27)))&(~m1_subset_1(X34,u1_struct_0(X28))|~r1_orders_2(X28,esk5_3(X27,X28,X32),X34)|~r2_hidden(k2_waybel_0(X27,X28,X34),X32)|r2_waybel_0(X27,X28,X32)|(v2_struct_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~l1_struct_0(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (r1_waybel_0(esk6_0,esk7_0,k4_xboole_0(u1_struct_0(esk6_0),X1))|r2_waybel_0(esk6_0,esk7_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.19/0.39  cnf(c_0_36, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (~r1_waybel_0(esk6_0,esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_39, plain, (r2_hidden(k2_waybel_0(X1,X2,esk4_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (r2_waybel_0(esk6_0,esk7_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.19/0.39  fof(c_0_41, plain, ![X14]:m1_subset_1(esk2_1(X14),X14), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.19/0.39  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_43, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_36])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,k1_xboole_0,X1)),k1_xboole_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.19/0.39  cnf(c_0_45, plain, (m1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.39  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(k2_waybel_0(esk6_0,esk7_0,esk4_4(esk6_0,esk7_0,k1_xboole_0,esk2_1(u1_struct_0(esk7_0)))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_47])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 49
% 0.19/0.39  # Proof object clause steps            : 28
% 0.19/0.39  # Proof object formula steps           : 21
% 0.19/0.39  # Proof object conjectures             : 13
% 0.19/0.39  # Proof object clause conjectures      : 10
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 11
% 0.19/0.39  # Proof object simplifying inferences  : 13
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 11
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 26
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 25
% 0.19/0.39  # Processed clauses                    : 113
% 0.19/0.39  # ...of these trivial                  : 4
% 0.19/0.39  # ...subsumed                          : 8
% 0.19/0.39  # ...remaining for further processing  : 101
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 125
% 0.19/0.39  # ...of the previous two non-trivial   : 100
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 125
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 75
% 0.19/0.39  #    Positive orientable unit clauses  : 24
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 48
% 0.19/0.39  # Current number of unprocessed clauses: 35
% 0.19/0.39  # ...number of literals in the above   : 72
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 27
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 626
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 161
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.39  # Unit Clause-clause subsumption calls : 6
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 18
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 4218
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.041 s
% 0.19/0.39  # System time              : 0.008 s
% 0.19/0.39  # Total time               : 0.049 s
% 0.19/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

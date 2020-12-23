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
% DateTime   : Thu Dec  3 11:09:28 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of clauses        :   29 (  32 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 304 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t24_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(d4_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
      <=> r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_11,plain,(
    ! [X28,X29,X32,X34,X35] :
      ( ( ~ v1_relat_1(X28)
        | ~ r2_hidden(X29,X28)
        | X29 = k4_tarski(esk6_2(X28,X29),esk7_2(X28,X29)) )
      & ( r2_hidden(esk8_1(X32),X32)
        | v1_relat_1(X32) )
      & ( esk8_1(X32) != k4_tarski(X34,X35)
        | v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10,X13,X14,X15,X16,X17,X18,X20,X21] :
      ( ( r2_hidden(esk1_4(X7,X8,X9,X10),X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( r2_hidden(esk2_4(X7,X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( X10 = k4_tarski(esk1_4(X7,X8,X9,X10),esk2_4(X7,X8,X9,X10))
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( ~ r2_hidden(X14,X7)
        | ~ r2_hidden(X15,X8)
        | X13 != k4_tarski(X14,X15)
        | r2_hidden(X13,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(X20,X16)
        | ~ r2_hidden(X21,X17)
        | esk3_3(X16,X17,X18) != k4_tarski(X20,X21)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk4_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk5_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( esk3_3(X16,X17,X18) = k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18))
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_13,plain,
    ( v1_relat_1(X1)
    | esk8_1(X1) != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( v1_relat_1(X1)
    | X2 != k2_zfmisc_1(X3,X4)
    | esk8_1(X1) != X5
    | ~ r2_hidden(X5,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_16,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | v1_relat_1(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_17,plain,(
    ! [X47] :
      ( ~ l1_orders_2(X47)
      | m1_subset_1(u1_orders_2(X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X47)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | esk8_1(X1) != X2
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X4)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(esk8_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r1_orders_2(X1,X2,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t24_orders_2])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2))
    | v1_relat_1(X3)
    | esk8_1(X3) != esk8_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk10_0)
    & v3_orders_2(esk10_0)
    & l1_orders_2(esk10_0)
    & m1_subset_1(esk11_0,u1_struct_0(esk10_0))
    & ~ r1_orders_2(esk10_0,esk11_0,esk11_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_25,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r1_orders_2(X43,X44,X45)
        | r2_hidden(k4_tarski(X44,X45),u1_orders_2(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ l1_orders_2(X43) )
      & ( ~ r2_hidden(k4_tarski(X44,X45),u1_orders_2(X43))
        | r1_orders_2(X43,X44,X45)
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ l1_orders_2(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

fof(c_0_26,plain,(
    ! [X36,X37,X38,X39] :
      ( ( ~ r1_relat_2(X36,X37)
        | ~ r2_hidden(X38,X37)
        | r2_hidden(k4_tarski(X38,X38),X36)
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(esk9_2(X36,X39),X39)
        | r1_relat_2(X36,X39)
        | ~ v1_relat_1(X36) )
      & ( ~ r2_hidden(k4_tarski(esk9_2(X36,X39),esk9_2(X36,X39)),X36)
        | r1_relat_2(X36,X39)
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

fof(c_0_27,plain,(
    ! [X42] :
      ( ( ~ v3_orders_2(X42)
        | r1_relat_2(u1_orders_2(X42),u1_struct_0(X42))
        | ~ l1_orders_2(X42) )
      & ( ~ r1_relat_2(u1_orders_2(X42),u1_struct_0(X42))
        | v3_orders_2(X42)
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).

cnf(c_0_28,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_orders_2(esk10_0,esk11_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( l1_orders_2(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk11_0,u1_struct_0(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X3,X3),X1)
    | ~ r1_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])])).

fof(c_0_37,plain,(
    ! [X41] :
      ( v2_struct_0(X41)
      | ~ l1_struct_0(X41)
      | ~ v1_xboole_0(u1_struct_0(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk11_0,esk11_0),u1_orders_2(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( v3_orders_2(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_41,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,X25)
      | v1_xboole_0(X25)
      | r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk11_0,u1_struct_0(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_32])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ l1_struct_0(esk10_0)
    | ~ v1_xboole_0(u1_struct_0(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_33])])).

fof(c_0_48,plain,(
    ! [X46] :
      ( ~ l1_orders_2(X46)
      | l1_struct_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_49,negated_conjecture,
    ( ~ l1_struct_0(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:14:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.14/0.39  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.14/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.39  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.14/0.39  fof(t24_orders_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.14/0.39  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.14/0.39  fof(d1_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_relat_2(X1,X2)<=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(k4_tarski(X3,X3),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 0.14/0.39  fof(d4_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v3_orders_2(X1)<=>r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_orders_2)).
% 0.14/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.39  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.39  fof(c_0_11, plain, ![X28, X29, X32, X34, X35]:((~v1_relat_1(X28)|(~r2_hidden(X29,X28)|X29=k4_tarski(esk6_2(X28,X29),esk7_2(X28,X29))))&((r2_hidden(esk8_1(X32),X32)|v1_relat_1(X32))&(esk8_1(X32)!=k4_tarski(X34,X35)|v1_relat_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.14/0.39  fof(c_0_12, plain, ![X7, X8, X9, X10, X13, X14, X15, X16, X17, X18, X20, X21]:(((((r2_hidden(esk1_4(X7,X8,X9,X10),X7)|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8))&(r2_hidden(esk2_4(X7,X8,X9,X10),X8)|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8)))&(X10=k4_tarski(esk1_4(X7,X8,X9,X10),esk2_4(X7,X8,X9,X10))|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8)))&(~r2_hidden(X14,X7)|~r2_hidden(X15,X8)|X13!=k4_tarski(X14,X15)|r2_hidden(X13,X9)|X9!=k2_zfmisc_1(X7,X8)))&((~r2_hidden(esk3_3(X16,X17,X18),X18)|(~r2_hidden(X20,X16)|~r2_hidden(X21,X17)|esk3_3(X16,X17,X18)!=k4_tarski(X20,X21))|X18=k2_zfmisc_1(X16,X17))&(((r2_hidden(esk4_3(X16,X17,X18),X16)|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17))&(r2_hidden(esk5_3(X16,X17,X18),X17)|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17)))&(esk3_3(X16,X17,X18)=k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18))|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.14/0.39  cnf(c_0_13, plain, (v1_relat_1(X1)|esk8_1(X1)!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_14, plain, (X1=k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_15, plain, (v1_relat_1(X1)|X2!=k2_zfmisc_1(X3,X4)|esk8_1(X1)!=X5|~r2_hidden(X5,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.39  fof(c_0_16, plain, ![X26, X27]:(~v1_relat_1(X26)|(~m1_subset_1(X27,k1_zfmisc_1(X26))|v1_relat_1(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.39  fof(c_0_17, plain, ![X47]:(~l1_orders_2(X47)|m1_subset_1(u1_orders_2(X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X47))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.14/0.39  cnf(c_0_18, plain, (v1_relat_1(X1)|esk8_1(X1)!=X2|~r2_hidden(X2,k2_zfmisc_1(X3,X4))), inference(er,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_19, plain, (r2_hidden(esk8_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  fof(c_0_20, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2)))), inference(assume_negation,[status(cth)],[t24_orders_2])).
% 0.14/0.39  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_22, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_23, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))|v1_relat_1(X3)|esk8_1(X3)!=esk8_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.39  fof(c_0_24, negated_conjecture, (((~v2_struct_0(esk10_0)&v3_orders_2(esk10_0))&l1_orders_2(esk10_0))&(m1_subset_1(esk11_0,u1_struct_0(esk10_0))&~r1_orders_2(esk10_0,esk11_0,esk11_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.14/0.39  fof(c_0_25, plain, ![X43, X44, X45]:((~r1_orders_2(X43,X44,X45)|r2_hidden(k4_tarski(X44,X45),u1_orders_2(X43))|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,u1_struct_0(X43))|~l1_orders_2(X43))&(~r2_hidden(k4_tarski(X44,X45),u1_orders_2(X43))|r1_orders_2(X43,X44,X45)|~m1_subset_1(X45,u1_struct_0(X43))|~m1_subset_1(X44,u1_struct_0(X43))|~l1_orders_2(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.14/0.39  fof(c_0_26, plain, ![X36, X37, X38, X39]:((~r1_relat_2(X36,X37)|(~r2_hidden(X38,X37)|r2_hidden(k4_tarski(X38,X38),X36))|~v1_relat_1(X36))&((r2_hidden(esk9_2(X36,X39),X39)|r1_relat_2(X36,X39)|~v1_relat_1(X36))&(~r2_hidden(k4_tarski(esk9_2(X36,X39),esk9_2(X36,X39)),X36)|r1_relat_2(X36,X39)|~v1_relat_1(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).
% 0.14/0.39  fof(c_0_27, plain, ![X42]:((~v3_orders_2(X42)|r1_relat_2(u1_orders_2(X42),u1_struct_0(X42))|~l1_orders_2(X42))&(~r1_relat_2(u1_orders_2(X42),u1_struct_0(X42))|v3_orders_2(X42)|~l1_orders_2(X42))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).
% 0.14/0.39  cnf(c_0_28, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)|~v1_relat_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.39  cnf(c_0_29, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (~r1_orders_2(esk10_0,esk11_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_31, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (l1_orders_2(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk11_0,u1_struct_0(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X3,X3),X1)|~r1_relat_2(X1,X2)|~r2_hidden(X3,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.39  cnf(c_0_35, plain, (r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.39  cnf(c_0_36, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29])])).
% 0.14/0.39  fof(c_0_37, plain, ![X41]:(v2_struct_0(X41)|~l1_struct_0(X41)|~v1_xboole_0(u1_struct_0(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (~r2_hidden(k4_tarski(esk11_0,esk11_0),u1_orders_2(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 0.14/0.39  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (v3_orders_2(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  fof(c_0_41, plain, ![X24, X25]:(~m1_subset_1(X24,X25)|(v1_xboole_0(X25)|r2_hidden(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_43, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk11_0,u1_struct_0(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_32])])).
% 0.14/0.39  cnf(c_0_45, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (~l1_struct_0(esk10_0)|~v1_xboole_0(u1_struct_0(esk10_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (v1_xboole_0(u1_struct_0(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_33])])).
% 0.14/0.39  fof(c_0_48, plain, ![X46]:(~l1_orders_2(X46)|l1_struct_0(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (~l1_struct_0(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])])).
% 0.14/0.39  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_32])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 52
% 0.14/0.39  # Proof object clause steps            : 29
% 0.14/0.39  # Proof object formula steps           : 23
% 0.14/0.39  # Proof object conjectures             : 14
% 0.14/0.39  # Proof object clause conjectures      : 11
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 16
% 0.14/0.39  # Proof object initial formulas used   : 11
% 0.14/0.39  # Proof object generating inferences   : 11
% 0.14/0.39  # Proof object simplifying inferences  : 15
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 11
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 28
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 28
% 0.14/0.39  # Processed clauses                    : 81
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 2
% 0.14/0.39  # ...remaining for further processing  : 79
% 0.14/0.39  # Other redundant clauses eliminated   : 2
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 4
% 0.14/0.39  # Generated clauses                    : 48
% 0.14/0.39  # ...of the previous two non-trivial   : 44
% 0.14/0.39  # Contextual simplify-reflections      : 1
% 0.14/0.39  # Paramodulations                      : 42
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 6
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 47
% 0.14/0.39  #    Positive orientable unit clauses  : 5
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 5
% 0.14/0.39  #    Non-unit-clauses                  : 37
% 0.14/0.39  # Current number of unprocessed clauses: 19
% 0.14/0.39  # ...number of literals in the above   : 90
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 32
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 205
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 47
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.39  # Unit Clause-clause subsumption calls : 37
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 3
% 0.14/0.39  # BW rewrite match successes           : 3
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 3143
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.031 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.036 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

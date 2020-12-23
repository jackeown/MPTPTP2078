%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:53 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of clauses        :   23 (  27 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 (  99 expanded)
%              Number of equality atoms :   30 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(t19_yellow_1,conjecture,(
    ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_13,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_14,plain,(
    ! [X15] :
      ( v1_orders_2(k2_yellow_1(X15))
      & l1_orders_2(k2_yellow_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_15,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | k2_struct_0(X12) = u1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_16,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X17] :
      ( u1_struct_0(k2_yellow_1(X17)) = X17
      & u1_orders_2(k2_yellow_1(X17)) = k1_yellow_1(X17) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_19,plain,(
    ! [X16] :
      ( v1_xboole_0(X16)
      | ~ r2_hidden(k3_tarski(X16),X16)
      | k4_yellow_0(k2_yellow_1(X16)) = k3_tarski(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_20,plain,(
    ! [X3,X4,X5] :
      ( ( ~ v1_xboole_0(X3)
        | ~ r2_hidden(X4,X3) )
      & ( r2_hidden(esk1_1(X5),X5)
        | v1_xboole_0(X5) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | m1_subset_1(k2_struct_0(X13),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_22,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( l1_struct_0(k2_yellow_1(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] : k4_yellow_0(k3_yellow_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t19_yellow_1])).

fof(c_0_26,plain,(
    ! [X18] : k3_yellow_1(X18) = k2_yellow_1(k9_setfam_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_27,plain,(
    ! [X11] : k9_setfam_1(X11) = k1_zfmisc_1(X11) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X7] : k3_tarski(k1_zfmisc_1(X7)) = X7 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X9,X10)
      | v1_xboole_0(X10)
      | r2_hidden(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k2_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_34,plain,(
    ! [X8] : ~ v1_xboole_0(k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_35,negated_conjecture,(
    k4_yellow_0(k3_yellow_1(esk2_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_36,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_33]),c_0_24])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k4_yellow_0(k3_yellow_1(esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1))) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(esk2_0))) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 15:40:06 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S058I
% 0.11/0.35  # and selection function PSelectMin2Infpos.
% 0.11/0.35  #
% 0.11/0.35  # Preprocessing time       : 0.027 s
% 0.11/0.35  # Presaturation interreduction done
% 0.11/0.35  
% 0.11/0.35  # Proof found!
% 0.11/0.35  # SZS status Theorem
% 0.11/0.35  # SZS output start CNFRefutation
% 0.11/0.35  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.11/0.35  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.11/0.35  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.11/0.35  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.11/0.35  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.11/0.35  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.11/0.35  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.11/0.35  fof(t19_yellow_1, conjecture, ![X1]:k4_yellow_0(k3_yellow_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 0.11/0.35  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.11/0.35  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.11/0.35  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.11/0.35  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.11/0.35  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.11/0.35  fof(c_0_13, plain, ![X14]:(~l1_orders_2(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.11/0.35  fof(c_0_14, plain, ![X15]:(v1_orders_2(k2_yellow_1(X15))&l1_orders_2(k2_yellow_1(X15))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.11/0.35  fof(c_0_15, plain, ![X12]:(~l1_struct_0(X12)|k2_struct_0(X12)=u1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.11/0.35  cnf(c_0_16, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.35  cnf(c_0_17, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.35  fof(c_0_18, plain, ![X17]:(u1_struct_0(k2_yellow_1(X17))=X17&u1_orders_2(k2_yellow_1(X17))=k1_yellow_1(X17)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.11/0.35  fof(c_0_19, plain, ![X16]:(v1_xboole_0(X16)|(~r2_hidden(k3_tarski(X16),X16)|k4_yellow_0(k2_yellow_1(X16))=k3_tarski(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.11/0.35  fof(c_0_20, plain, ![X3, X4, X5]:((~v1_xboole_0(X3)|~r2_hidden(X4,X3))&(r2_hidden(esk1_1(X5),X5)|v1_xboole_0(X5))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.11/0.35  fof(c_0_21, plain, ![X13]:(~l1_struct_0(X13)|m1_subset_1(k2_struct_0(X13),k1_zfmisc_1(u1_struct_0(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.11/0.35  cnf(c_0_22, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.35  cnf(c_0_23, plain, (l1_struct_0(k2_yellow_1(X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.35  cnf(c_0_24, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.11/0.35  fof(c_0_25, negated_conjecture, ~(![X1]:k4_yellow_0(k3_yellow_1(X1))=X1), inference(assume_negation,[status(cth)],[t19_yellow_1])).
% 0.11/0.35  fof(c_0_26, plain, ![X18]:k3_yellow_1(X18)=k2_yellow_1(k9_setfam_1(X18)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.11/0.35  fof(c_0_27, plain, ![X11]:k9_setfam_1(X11)=k1_zfmisc_1(X11), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.11/0.35  cnf(c_0_28, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.35  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.35  fof(c_0_30, plain, ![X7]:k3_tarski(k1_zfmisc_1(X7))=X7, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.11/0.35  fof(c_0_31, plain, ![X9, X10]:(~m1_subset_1(X9,X10)|(v1_xboole_0(X10)|r2_hidden(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.11/0.35  cnf(c_0_32, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.35  cnf(c_0_33, plain, (k2_struct_0(k2_yellow_1(X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.11/0.35  fof(c_0_34, plain, ![X8]:~v1_xboole_0(k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.11/0.35  fof(c_0_35, negated_conjecture, k4_yellow_0(k3_yellow_1(esk2_0))!=esk2_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.11/0.35  cnf(c_0_36, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.35  cnf(c_0_37, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.11/0.35  cnf(c_0_38, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.11/0.35  cnf(c_0_39, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.11/0.35  cnf(c_0_40, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.11/0.35  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_23]), c_0_33]), c_0_24])).
% 0.11/0.35  cnf(c_0_42, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.11/0.35  cnf(c_0_43, negated_conjecture, (k4_yellow_0(k3_yellow_1(esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.11/0.35  cnf(c_0_44, plain, (k3_yellow_1(X1)=k2_yellow_1(k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.11/0.35  cnf(c_0_45, plain, (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1)))=X1|~r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.11/0.35  cnf(c_0_46, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.11/0.35  cnf(c_0_47, negated_conjecture, (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(esk2_0)))!=esk2_0), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.11/0.35  cnf(c_0_48, plain, (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(X1)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.11/0.35  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])]), ['proof']).
% 0.11/0.35  # SZS output end CNFRefutation
% 0.11/0.35  # Proof object total steps             : 50
% 0.11/0.35  # Proof object clause steps            : 23
% 0.11/0.35  # Proof object formula steps           : 27
% 0.11/0.35  # Proof object conjectures             : 6
% 0.11/0.35  # Proof object clause conjectures      : 3
% 0.11/0.35  # Proof object formula conjectures     : 3
% 0.11/0.35  # Proof object initial clauses used    : 13
% 0.11/0.35  # Proof object initial formulas used   : 13
% 0.11/0.35  # Proof object generating inferences   : 5
% 0.11/0.35  # Proof object simplifying inferences  : 11
% 0.11/0.35  # Training examples: 0 positive, 0 negative
% 0.11/0.35  # Parsed axioms                        : 13
% 0.11/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.35  # Initial clauses                      : 16
% 0.11/0.35  # Removed in clause preprocessing      : 3
% 0.11/0.35  # Initial clauses in saturation        : 13
% 0.11/0.35  # Processed clauses                    : 32
% 0.11/0.35  # ...of these trivial                  : 0
% 0.11/0.35  # ...subsumed                          : 0
% 0.11/0.35  # ...remaining for further processing  : 32
% 0.11/0.35  # Other redundant clauses eliminated   : 0
% 0.11/0.35  # Clauses deleted for lack of memory   : 0
% 0.11/0.35  # Backward-subsumed                    : 0
% 0.11/0.35  # Backward-rewritten                   : 2
% 0.11/0.35  # Generated clauses                    : 9
% 0.11/0.35  # ...of the previous two non-trivial   : 8
% 0.11/0.35  # Contextual simplify-reflections      : 1
% 0.11/0.35  # Paramodulations                      : 9
% 0.11/0.35  # Factorizations                       : 0
% 0.11/0.35  # Equation resolutions                 : 0
% 0.11/0.35  # Propositional unsat checks           : 0
% 0.11/0.35  #    Propositional check models        : 0
% 0.11/0.35  #    Propositional check unsatisfiable : 0
% 0.11/0.35  #    Propositional clauses             : 0
% 0.11/0.35  #    Propositional clauses after purity: 0
% 0.11/0.35  #    Propositional unsat core size     : 0
% 0.11/0.35  #    Propositional preprocessing time  : 0.000
% 0.11/0.35  #    Propositional encoding time       : 0.000
% 0.11/0.35  #    Propositional solver time         : 0.000
% 0.11/0.35  #    Success case prop preproc time    : 0.000
% 0.11/0.35  #    Success case prop encoding time   : 0.000
% 0.11/0.35  #    Success case prop solver time     : 0.000
% 0.11/0.35  # Current number of processed clauses  : 17
% 0.11/0.35  #    Positive orientable unit clauses  : 9
% 0.11/0.35  #    Positive unorientable unit clauses: 0
% 0.11/0.35  #    Negative unit clauses             : 1
% 0.11/0.35  #    Non-unit-clauses                  : 7
% 0.11/0.35  # Current number of unprocessed clauses: 2
% 0.11/0.35  # ...number of literals in the above   : 2
% 0.11/0.35  # Current number of archived formulas  : 0
% 0.11/0.35  # Current number of archived clauses   : 18
% 0.11/0.35  # Clause-clause subsumption calls (NU) : 7
% 0.11/0.35  # Rec. Clause-clause subsumption calls : 5
% 0.11/0.35  # Non-unit clause-clause subsumptions  : 1
% 0.11/0.35  # Unit Clause-clause subsumption calls : 1
% 0.11/0.35  # Rewrite failures with RHS unbound    : 0
% 0.11/0.35  # BW rewrite match attempts            : 3
% 0.11/0.35  # BW rewrite match successes           : 2
% 0.11/0.35  # Condensation attempts                : 0
% 0.11/0.35  # Condensation successes               : 0
% 0.11/0.35  # Termbank termtop insertions          : 923
% 0.11/0.35  
% 0.11/0.35  # -------------------------------------------------
% 0.11/0.35  # User time                : 0.027 s
% 0.11/0.35  # System time              : 0.004 s
% 0.11/0.35  # Total time               : 0.031 s
% 0.11/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

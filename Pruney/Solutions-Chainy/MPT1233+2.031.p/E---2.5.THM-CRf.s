%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:44 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 301 expanded)
%              Number of clauses        :   49 ( 134 expanded)
%              Number of leaves         :   23 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  198 ( 553 expanded)
%              Number of equality atoms :   67 ( 229 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(t43_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t27_pre_topc,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = k3_subset_1(u1_struct_0(X1),k1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

fof(fc3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => v1_xboole_0(k1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(cc2_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(c_0_23,plain,(
    ! [X18,X19] : m1_subset_1(k6_subset_1(X18,X19),k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_24,plain,(
    ! [X22,X23] : k6_subset_1(X22,X23) = k4_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_25,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_26,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_27,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | ~ v1_xboole_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_29])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X30,X32,X33,X34] :
      ( ( r2_hidden(esk1_1(X30),X30)
        | X30 = k1_xboole_0 )
      & ( ~ r2_hidden(X32,X30)
        | esk1_1(X30) != k3_mcart_1(X32,X33,X34)
        | X30 = k1_xboole_0 )
      & ( ~ r2_hidden(X33,X30)
        | esk1_1(X30) != k3_mcart_1(X32,X33,X34)
        | X30 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_38,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | X13 = X14
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t43_tops_1])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X12] : k5_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_46,plain,(
    ! [X38] :
      ( ~ l1_pre_topc(X38)
      | l1_struct_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & k1_tops_1(esk2_0,k2_struct_0(esk2_0)) != k2_struct_0(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_48,plain,(
    ! [X24] : k2_subset_1(X24) = k3_subset_1(X24,k1_subset_1(X24)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_49,plain,(
    ! [X17] : k2_subset_1(X17) = X17 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_50,plain,(
    ! [X16] : k1_subset_1(X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_51,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_56,plain,(
    ! [X40] :
      ( ~ l1_struct_0(X40)
      | k2_struct_0(X40) = k3_subset_1(u1_struct_0(X40),k1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_pre_topc])])).

cnf(c_0_57,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_59,plain,(
    ! [X39] :
      ( ~ l1_struct_0(X39)
      | v1_xboole_0(k1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).

fof(c_0_60,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | k3_subset_1(X20,k3_subset_1(X20,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_61,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( k1_tops_1(esk2_0,k2_struct_0(esk2_0)) != k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_67,plain,
    ( k2_struct_0(X1) = k3_subset_1(u1_struct_0(X1),k1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,plain,
    ( v1_xboole_0(k1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_73,plain,(
    ! [X35,X36] :
      ( ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | ~ v1_xboole_0(X36)
      | v4_pre_topc(X36,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).

cnf(c_0_74,negated_conjecture,
    ( k1_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),k1_struct_0(esk2_0))) != k3_subset_1(u1_struct_0(esk2_0),k1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_75,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_69])).

fof(c_0_76,plain,(
    ! [X43,X44] :
      ( ~ l1_pre_topc(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | k1_tops_1(X43,X44) = k3_subset_1(u1_struct_0(X43),k2_pre_topc(X43,k3_subset_1(u1_struct_0(X43),X44))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_77,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_45])).

fof(c_0_79,plain,(
    ! [X41,X42] :
      ( ( ~ v4_pre_topc(X42,X41)
        | k2_pre_topc(X41,X42) = X42
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) )
      & ( ~ v2_pre_topc(X41)
        | k2_pre_topc(X41,X42) != X42
        | v4_pre_topc(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_80,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( k1_tops_1(esk2_0,u1_struct_0(esk2_0)) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_71]),c_0_71]),c_0_68])])).

cnf(c_0_83,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78])])).

cnf(c_0_85,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( v4_pre_topc(X1,esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_58])]),c_0_72])).

fof(c_0_87,plain,(
    ! [X37] :
      ( ~ l1_struct_0(X37)
      | m1_subset_1(k2_struct_0(X37),k1_zfmisc_1(u1_struct_0(X37))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_88,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k1_xboole_0)) != u1_struct_0(esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_58])]),c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( k2_pre_topc(esk2_0,X1) = X1
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_58])]),c_0_72])).

cnf(c_0_90,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_91,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_75]),c_0_71])).

cnf(c_0_92,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_71]),c_0_45])])).

cnf(c_0_93,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:08:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.21/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.21/0.39  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.21/0.39  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.21/0.39  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.39  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.21/0.39  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.21/0.39  fof(t43_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 0.21/0.39  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.39  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.21/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.21/0.39  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.21/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.39  fof(t27_pre_topc, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=k3_subset_1(u1_struct_0(X1),k1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 0.21/0.39  fof(fc3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>v1_xboole_0(k1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 0.21/0.39  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.21/0.39  fof(cc2_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 0.21/0.39  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 0.21/0.39  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.21/0.39  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.21/0.39  fof(c_0_23, plain, ![X18, X19]:m1_subset_1(k6_subset_1(X18,X19),k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.21/0.39  fof(c_0_24, plain, ![X22, X23]:k6_subset_1(X22,X23)=k4_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.21/0.39  fof(c_0_25, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.39  fof(c_0_26, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.39  cnf(c_0_27, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_28, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.39  fof(c_0_31, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|~v1_xboole_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.21/0.39  cnf(c_0_32, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.21/0.39  cnf(c_0_33, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29]), c_0_29])).
% 0.21/0.39  fof(c_0_34, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.39  cnf(c_0_35, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.39  cnf(c_0_36, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.39  fof(c_0_37, plain, ![X30, X32, X33, X34]:((r2_hidden(esk1_1(X30),X30)|X30=k1_xboole_0)&((~r2_hidden(X32,X30)|esk1_1(X30)!=k3_mcart_1(X32,X33,X34)|X30=k1_xboole_0)&(~r2_hidden(X33,X30)|esk1_1(X30)!=k3_mcart_1(X32,X33,X34)|X30=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.21/0.39  fof(c_0_38, plain, ![X13, X14]:(~v1_xboole_0(X13)|X13=X14|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.21/0.39  fof(c_0_39, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1))), inference(assume_negation,[status(cth)],[t43_tops_1])).
% 0.21/0.39  cnf(c_0_40, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.39  cnf(c_0_41, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.39  cnf(c_0_42, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.39  fof(c_0_43, plain, ![X12]:k5_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.39  cnf(c_0_44, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.39  cnf(c_0_45, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.39  fof(c_0_46, plain, ![X38]:(~l1_pre_topc(X38)|l1_struct_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.39  fof(c_0_47, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&k1_tops_1(esk2_0,k2_struct_0(esk2_0))!=k2_struct_0(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.21/0.39  fof(c_0_48, plain, ![X24]:k2_subset_1(X24)=k3_subset_1(X24,k1_subset_1(X24)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.21/0.39  fof(c_0_49, plain, ![X17]:k2_subset_1(X17)=X17, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.21/0.39  fof(c_0_50, plain, ![X16]:k1_subset_1(X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.21/0.39  fof(c_0_51, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.39  cnf(c_0_52, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_40, c_0_29])).
% 0.21/0.39  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.39  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.39  cnf(c_0_55, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.39  fof(c_0_56, plain, ![X40]:(~l1_struct_0(X40)|k2_struct_0(X40)=k3_subset_1(u1_struct_0(X40),k1_struct_0(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_pre_topc])])).
% 0.21/0.39  cnf(c_0_57, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  fof(c_0_59, plain, ![X39]:(~l1_struct_0(X39)|v1_xboole_0(k1_struct_0(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).
% 0.21/0.39  fof(c_0_60, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|k3_subset_1(X20,k3_subset_1(X20,X21))=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.21/0.39  cnf(c_0_61, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.39  cnf(c_0_62, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.39  cnf(c_0_63, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.39  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.39  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (k1_tops_1(esk2_0,k2_struct_0(esk2_0))!=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_67, plain, (k2_struct_0(X1)=k3_subset_1(u1_struct_0(X1),k1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.39  cnf(c_0_68, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.39  cnf(c_0_69, plain, (v1_xboole_0(k1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.39  cnf(c_0_70, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.39  cnf(c_0_71, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.21/0.39  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.39  fof(c_0_73, plain, ![X35, X36]:(~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(~v1_xboole_0(X36)|v4_pre_topc(X36,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).
% 0.21/0.39  cnf(c_0_74, negated_conjecture, (k1_tops_1(esk2_0,k3_subset_1(u1_struct_0(esk2_0),k1_struct_0(esk2_0)))!=k3_subset_1(u1_struct_0(esk2_0),k1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.21/0.39  cnf(c_0_75, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_69])).
% 0.21/0.39  fof(c_0_76, plain, ![X43, X44]:(~l1_pre_topc(X43)|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|k1_tops_1(X43,X44)=k3_subset_1(u1_struct_0(X43),k2_pre_topc(X43,k3_subset_1(u1_struct_0(X43),X44))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.21/0.39  cnf(c_0_77, plain, (k3_subset_1(X1,X1)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.21/0.39  cnf(c_0_78, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_72, c_0_45])).
% 0.21/0.39  fof(c_0_79, plain, ![X41, X42]:((~v4_pre_topc(X42,X41)|k2_pre_topc(X41,X42)=X42|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X41))&(~v2_pre_topc(X41)|k2_pre_topc(X41,X42)!=X42|v4_pre_topc(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.21/0.39  cnf(c_0_80, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.21/0.39  cnf(c_0_81, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_82, negated_conjecture, (k1_tops_1(esk2_0,u1_struct_0(esk2_0))!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_71]), c_0_71]), c_0_68])])).
% 0.21/0.39  cnf(c_0_83, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.21/0.39  cnf(c_0_84, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78])])).
% 0.21/0.39  cnf(c_0_85, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.21/0.39  cnf(c_0_86, negated_conjecture, (v4_pre_topc(X1,esk2_0)|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_58])]), c_0_72])).
% 0.21/0.39  fof(c_0_87, plain, ![X37]:(~l1_struct_0(X37)|m1_subset_1(k2_struct_0(X37),k1_zfmisc_1(u1_struct_0(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.21/0.39  cnf(c_0_88, negated_conjecture, (k3_subset_1(u1_struct_0(esk2_0),k2_pre_topc(esk2_0,k1_xboole_0))!=u1_struct_0(esk2_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_58])]), c_0_84])).
% 0.21/0.39  cnf(c_0_89, negated_conjecture, (k2_pre_topc(esk2_0,X1)=X1|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_58])]), c_0_72])).
% 0.21/0.39  cnf(c_0_90, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.21/0.39  cnf(c_0_91, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_75]), c_0_71])).
% 0.21/0.39  cnf(c_0_92, negated_conjecture, (~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_71]), c_0_45])])).
% 0.21/0.39  cnf(c_0_93, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.21/0.39  cnf(c_0_94, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_68])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 95
% 0.21/0.39  # Proof object clause steps            : 49
% 0.21/0.39  # Proof object formula steps           : 46
% 0.21/0.39  # Proof object conjectures             : 14
% 0.21/0.39  # Proof object clause conjectures      : 11
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 25
% 0.21/0.39  # Proof object initial formulas used   : 23
% 0.21/0.39  # Proof object generating inferences   : 19
% 0.21/0.39  # Proof object simplifying inferences  : 32
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 24
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 31
% 0.21/0.39  # Removed in clause preprocessing      : 4
% 0.21/0.39  # Initial clauses in saturation        : 27
% 0.21/0.39  # Processed clauses                    : 245
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 106
% 0.21/0.39  # ...remaining for further processing  : 138
% 0.21/0.39  # Other redundant clauses eliminated   : 0
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 2
% 0.21/0.39  # Backward-rewritten                   : 9
% 0.21/0.39  # Generated clauses                    : 353
% 0.21/0.39  # ...of the previous two non-trivial   : 315
% 0.21/0.39  # Contextual simplify-reflections      : 7
% 0.21/0.39  # Paramodulations                      : 344
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 0
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 97
% 0.21/0.39  #    Positive orientable unit clauses  : 17
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 8
% 0.21/0.39  #    Non-unit-clauses                  : 72
% 0.21/0.39  # Current number of unprocessed clauses: 114
% 0.21/0.39  # ...number of literals in the above   : 389
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 42
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1457
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 996
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 95
% 0.21/0.39  # Unit Clause-clause subsumption calls : 110
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 16
% 0.21/0.39  # BW rewrite match successes           : 6
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 6849
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.039 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.043 s
% 0.21/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

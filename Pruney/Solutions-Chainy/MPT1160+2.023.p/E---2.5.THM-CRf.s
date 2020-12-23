%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:56 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 688 expanded)
%              Number of clauses        :   43 ( 230 expanded)
%              Number of leaves         :   11 ( 171 expanded)
%              Depth                    :   19
%              Number of atoms          :  220 (3578 expanded)
%              Number of equality atoms :   21 ( 394 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t60_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_orders_2(X1,k1_struct_0(X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t57_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(fc3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => v1_xboole_0(k1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( v2_struct_0(X16)
      | ~ v3_orders_2(X16)
      | ~ v4_orders_2(X16)
      | ~ v5_orders_2(X16)
      | ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | m1_subset_1(k3_orders_2(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

fof(c_0_12,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k3_orders_2(X1,k1_struct_0(X1),X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t60_orders_2])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,k1_xboole_0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | m1_subset_1(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_26,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_orders_2(X20,X21,X22)
        | ~ r2_hidden(X21,k3_orders_2(X20,X23,X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20) )
      & ( r2_hidden(X21,X23)
        | ~ r2_hidden(X21,k3_orders_2(X20,X23,X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20) )
      & ( ~ r2_orders_2(X20,X21,X22)
        | ~ r2_hidden(X21,X23)
        | r2_hidden(X21,k3_orders_2(X20,X23,X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_25]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k3_orders_2(X3,X2,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_31,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk2_0,k1_xboole_0,esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X2)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_30])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_34,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_35,negated_conjecture,
    ( k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1) = k1_xboole_0
    | r2_hidden(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1)),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1) = k1_xboole_0
    | m1_subset_1(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1)),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_xboole_0)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k3_orders_2(X1,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0) = k1_xboole_0
    | r2_hidden(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0) = k1_xboole_0
    | m1_subset_1(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0) = k1_xboole_0
    | r2_hidden(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_18])]),c_0_23]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1),X2),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_28]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_47,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_48,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | v1_xboole_0(k1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,k1_xboole_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_18])])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_52,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X2))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X2),X3)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_49])).

cnf(c_0_55,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,k1_xboole_0,X2)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_18])]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k3_orders_2(esk2_0,k1_xboole_0,X1) = k1_xboole_0
    | r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,X1)),k1_xboole_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( k3_orders_2(esk2_0,k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_19])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_18]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_62])).

cnf(c_0_64,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_44,c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:36:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.19/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.38  fof(t60_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_orders_2(X1,k1_struct_0(X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 0.19/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.38  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 0.19/0.38  fof(fc3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>v1_xboole_0(k1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 0.19/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.38  fof(c_0_11, plain, ![X16, X17, X18]:(v2_struct_0(X16)|~v3_orders_2(X16)|~v4_orders_2(X16)|~v5_orders_2(X16)|~l1_orders_2(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~m1_subset_1(X18,u1_struct_0(X16))|m1_subset_1(k3_orders_2(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.19/0.38  fof(c_0_12, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_orders_2(X1,k1_struct_0(X1),X2)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t60_orders_2])).
% 0.19/0.38  cnf(c_0_14, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_15, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_16, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.38  cnf(c_0_17, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,k1_xboole_0,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_24, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|m1_subset_1(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.19/0.38  fof(c_0_26, plain, ![X20, X21, X22, X23]:(((r2_orders_2(X20,X21,X22)|~r2_hidden(X21,k3_orders_2(X20,X23,X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)))&(r2_hidden(X21,X23)|~r2_hidden(X21,k3_orders_2(X20,X23,X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20))))&(~r2_orders_2(X20,X21,X22)|~r2_hidden(X21,X23)|r2_hidden(X21,k3_orders_2(X20,X23,X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|~m1_subset_1(X22,u1_struct_0(X20))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.19/0.38  cnf(c_0_27, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_25]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  fof(c_0_31, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk2_0,k1_xboole_0,esk3_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X2))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_30])).
% 0.19/0.38  cnf(c_0_33, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  fof(c_0_34, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1)=k1_xboole_0|r2_hidden(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1)),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1)=k1_xboole_0|m1_subset_1(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1)),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.19/0.38  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_38, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_xboole_0)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X2,k3_orders_2(X1,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_29, c_0_15])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)=k1_xboole_0|r2_hidden(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_18])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)=k1_xboole_0|m1_subset_1(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_36, c_0_18])).
% 0.19/0.38  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_37, c_0_15])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)=k1_xboole_0|r2_hidden(esk1_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)),k1_xboole_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_18])]), c_0_23]), c_0_40])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_44, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X1),X2),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_28]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.38  fof(c_0_47, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.19/0.38  fof(c_0_48, plain, ![X15]:(~l1_struct_0(X15)|v1_xboole_0(k1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,k1_xboole_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_18])])).
% 0.19/0.38  cnf(c_0_50, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_51, plain, (v1_xboole_0(k1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.38  fof(c_0_52, plain, ![X19]:(~l1_orders_2(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X2))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k3_orders_2(esk2_0,k1_xboole_0,esk3_0),X2),X3))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_27, c_0_49])).
% 0.19/0.38  cnf(c_0_55, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.38  cnf(c_0_56, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,k1_xboole_0,X2))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_46]), c_0_18])]), c_0_54])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_59, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (k3_orders_2(esk2_0,k1_xboole_0,X1)=k1_xboole_0|r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,X1)),k1_xboole_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_57, c_0_33])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k3_orders_2(esk2_0,k1_xboole_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_19])])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_18]), c_0_61])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_62])).
% 0.19/0.38  cnf(c_0_64, plain, ($false), inference(sr,[status(thm)],[c_0_44, c_0_63]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 65
% 0.19/0.38  # Proof object clause steps            : 43
% 0.19/0.38  # Proof object formula steps           : 22
% 0.19/0.38  # Proof object conjectures             : 30
% 0.19/0.38  # Proof object clause conjectures      : 27
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 11
% 0.19/0.38  # Proof object generating inferences   : 25
% 0.19/0.38  # Proof object simplifying inferences  : 48
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 11
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 19
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 19
% 0.19/0.38  # Processed clauses                    : 122
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 23
% 0.19/0.38  # ...remaining for further processing  : 99
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 12
% 0.19/0.38  # Generated clauses                    : 164
% 0.19/0.38  # ...of the previous two non-trivial   : 148
% 0.19/0.38  # Contextual simplify-reflections      : 6
% 0.19/0.38  # Paramodulations                      : 163
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 67
% 0.19/0.38  #    Positive orientable unit clauses  : 11
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 5
% 0.19/0.38  #    Non-unit-clauses                  : 51
% 0.19/0.38  # Current number of unprocessed clauses: 59
% 0.19/0.38  # ...number of literals in the above   : 237
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 32
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1056
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 398
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 19
% 0.19/0.38  # Unit Clause-clause subsumption calls : 47
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 11
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7154
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.036 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

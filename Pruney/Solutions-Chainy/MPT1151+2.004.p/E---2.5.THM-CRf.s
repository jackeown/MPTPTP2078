%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:37 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 269 expanded)
%              Number of clauses        :   71 ( 121 expanded)
%              Number of leaves         :   15 (  69 expanded)
%              Depth                    :   31
%              Number of atoms          :  400 (1038 expanded)
%              Number of equality atoms :   37 (  93 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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

fof(t45_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k2_orders_2(X1,k1_struct_0(X1)) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k1_struct_0(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(fraenkel_a_2_1_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(d13_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(t49_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => r2_hidden(X3,X2) )
       => X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(dt_k2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(k1_zfmisc_1(X2),X3)
    | ~ r2_hidden(X1,esk1_2(k1_zfmisc_1(X2),X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X17] : m1_subset_1(esk2_1(X17),X17) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(esk1_2(k1_zfmisc_1(X1),X2))
    | r2_hidden(X3,X1)
    | r1_tarski(k1_zfmisc_1(X1),X2)
    | ~ m1_subset_1(X3,esk1_2(k1_zfmisc_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_32,plain,(
    ! [X12] :
      ( ~ v1_xboole_0(X12)
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(esk1_2(k1_zfmisc_1(X1),X2))
    | r2_hidden(esk2_1(esk1_2(k1_zfmisc_1(X1),X2)),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,plain,
    ( v1_xboole_0(esk1_2(k1_zfmisc_1(X1),X2))
    | r1_tarski(k1_zfmisc_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_33])).

cnf(c_0_36,plain,
    ( esk1_2(k1_zfmisc_1(X1),X2) = k1_xboole_0
    | r1_tarski(k1_zfmisc_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_zfmisc_1(X1),X2)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_36]),c_0_18])).

fof(c_0_38,plain,(
    ! [X25] :
      ( ~ l1_struct_0(X25)
      | v1_xboole_0(k1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_zfmisc_1(X1),X2)
    | r1_tarski(k1_xboole_0,X3)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_41,plain,(
    ! [X30] :
      ( ~ l1_orders_2(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k2_orders_2(X1,k1_struct_0(X1)) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t45_orders_2])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_zfmisc_1(k1_struct_0(X1)),X2)
    | r1_tarski(k1_xboole_0,X3)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & v5_orders_2(esk6_0)
    & l1_orders_2(esk6_0)
    & k2_orders_2(esk6_0,k1_struct_0(esk6_0)) != u1_struct_0(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_42])])])])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_zfmisc_1(k1_struct_0(X1)),X2)
    | r1_tarski(k1_xboole_0,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(k1_struct_0(esk6_0)),X1)
    | r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,X2)
    | r1_tarski(k1_xboole_0,X3)
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))
    | r2_hidden(X1,X2)
    | r1_tarski(k1_xboole_0,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))
    | r2_hidden(X1,X2)
    | r1_tarski(k1_xboole_0,X3)
    | ~ r1_tarski(X1,k1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))
    | r2_hidden(k1_struct_0(esk6_0),X1)
    | r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))
    | r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_55])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_59,plain,
    ( v1_xboole_0(esk2_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,plain,
    ( esk2_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_59])).

cnf(c_0_62,plain,
    ( r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_31])).

cnf(c_0_63,negated_conjecture,
    ( k1_zfmisc_1(k1_struct_0(esk6_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_60])).

cnf(c_0_64,plain,
    ( esk2_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_struct_0(esk6_0))
    | r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_struct_0(esk6_0)) ),
    inference(ef,[status(thm)],[c_0_65])).

fof(c_0_67,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | k1_struct_0(X24) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).

fof(c_0_68,plain,(
    ! [X31,X32,X33,X35,X36] :
      ( ( m1_subset_1(esk4_3(X31,X32,X33),u1_struct_0(X32))
        | ~ r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( X31 = esk4_3(X31,X32,X33)
        | ~ r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r2_hidden(X35,X33)
        | r2_orders_2(X32,esk4_3(X31,X32,X33),X35)
        | ~ r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( m1_subset_1(esk5_4(X31,X32,X33,X36),u1_struct_0(X32))
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( r2_hidden(esk5_4(X31,X32,X33,X36),X33)
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( ~ r2_orders_2(X32,X36,esk5_4(X31,X32,X33,X36))
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_69,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v3_orders_2(X26)
      | ~ v4_orders_2(X26)
      | ~ v5_orders_2(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | k2_orders_2(X26,X27) = a_2_1_orders_2(X26,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,k1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_66])).

cnf(c_0_71,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(k1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_70])).

cnf(c_0_75,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_44])).

fof(c_0_76,plain,(
    ! [X19,X20] :
      ( ( m1_subset_1(esk3_2(X19,X20),X19)
        | X19 = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(X19)) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | X19 = X20
        | ~ m1_subset_1(X20,k1_zfmisc_1(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk5_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_72])).

fof(c_0_78,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ v3_orders_2(X28)
      | ~ v4_orders_2(X28)
      | ~ v5_orders_2(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | m1_subset_1(k2_orders_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).

cnf(c_0_79,plain,
    ( k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_51])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_58]),c_0_47])])).

cnf(c_0_82,plain,
    ( X1 = X2
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_77])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k2_orders_2(esk6_0,k1_struct_0(esk6_0)) != u1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_22])).

cnf(c_0_88,plain,
    ( X1 = a_2_1_orders_2(X2,X3)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(esk3_2(X1,a_2_1_orders_2(X2,X3)),u1_struct_0(X2))
    | ~ m1_subset_1(a_2_1_orders_2(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,plain,
    ( m1_subset_1(esk3_2(X1,X2),X1)
    | X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(a_2_1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( k2_orders_2(esk6_0,k1_xboole_0) != u1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_75]),c_0_47])])).

cnf(c_0_92,negated_conjecture,
    ( k2_orders_2(X1,k1_xboole_0) = a_2_1_orders_2(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_94,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_95,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_96,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_97,plain,
    ( a_2_1_orders_2(X1,X2) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( a_2_1_orders_2(esk6_0,k1_xboole_0) != u1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_47]),c_0_93]),c_0_94]),c_0_95])]),c_0_96])).

cnf(c_0_99,plain,
    ( a_2_1_orders_2(X1,X2) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_51]),c_0_80])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_47]),c_0_93]),c_0_94]),c_0_95]),c_0_58])]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:07:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.82/1.03  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.82/1.03  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.82/1.03  #
% 0.82/1.03  # Preprocessing time       : 0.028 s
% 0.82/1.03  
% 0.82/1.03  # Proof found!
% 0.82/1.03  # SZS status Theorem
% 0.82/1.03  # SZS output start CNFRefutation
% 0.82/1.03  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.82/1.03  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.82/1.03  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.82/1.03  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.82/1.03  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.82/1.03  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.82/1.03  fof(fc3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>v1_xboole_0(k1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 0.82/1.03  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.82/1.03  fof(t45_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k2_orders_2(X1,k1_struct_0(X1))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_orders_2)).
% 0.82/1.03  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.82/1.03  fof(d2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k1_struct_0(X1)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 0.82/1.03  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.82/1.03  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 0.82/1.03  fof(t49_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(![X3]:(m1_subset_1(X3,X1)=>r2_hidden(X3,X2))=>X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 0.82/1.03  fof(dt_k2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 0.82/1.03  fof(c_0_15, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.82/1.03  fof(c_0_16, plain, ![X13, X14]:(~r2_hidden(X13,X14)|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.82/1.03  cnf(c_0_17, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.82/1.03  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.82/1.03  fof(c_0_19, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.82/1.03  fof(c_0_20, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.82/1.03  cnf(c_0_21, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.82/1.03  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.82/1.03  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.82/1.03  cnf(c_0_24, plain, (m1_subset_1(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.82/1.03  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.82/1.03  cnf(c_0_26, plain, (r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.82/1.03  cnf(c_0_27, plain, (r2_hidden(X1,X2)|r1_tarski(k1_zfmisc_1(X2),X3)|~r2_hidden(X1,esk1_2(k1_zfmisc_1(X2),X3))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.82/1.03  cnf(c_0_28, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.82/1.03  fof(c_0_29, plain, ![X17]:m1_subset_1(esk2_1(X17),X17), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.82/1.03  cnf(c_0_30, plain, (v1_xboole_0(esk1_2(k1_zfmisc_1(X1),X2))|r2_hidden(X3,X1)|r1_tarski(k1_zfmisc_1(X1),X2)|~m1_subset_1(X3,esk1_2(k1_zfmisc_1(X1),X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.82/1.03  cnf(c_0_31, plain, (m1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.82/1.03  fof(c_0_32, plain, ![X12]:(~v1_xboole_0(X12)|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.82/1.03  cnf(c_0_33, plain, (v1_xboole_0(esk1_2(k1_zfmisc_1(X1),X2))|r2_hidden(esk2_1(esk1_2(k1_zfmisc_1(X1),X2)),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.82/1.03  cnf(c_0_34, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.82/1.03  cnf(c_0_35, plain, (v1_xboole_0(esk1_2(k1_zfmisc_1(X1),X2))|r1_tarski(k1_zfmisc_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_18, c_0_33])).
% 0.82/1.03  cnf(c_0_36, plain, (esk1_2(k1_zfmisc_1(X1),X2)=k1_xboole_0|r1_tarski(k1_zfmisc_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.82/1.03  cnf(c_0_37, plain, (r1_tarski(k1_zfmisc_1(X1),X2)|~v1_xboole_0(X1)|~r2_hidden(X3,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_36]), c_0_18])).
% 0.82/1.03  fof(c_0_38, plain, ![X25]:(~l1_struct_0(X25)|v1_xboole_0(k1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_struct_0])])).
% 0.82/1.03  cnf(c_0_39, plain, (r1_tarski(k1_zfmisc_1(X1),X2)|r1_tarski(k1_xboole_0,X3)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_22])).
% 0.82/1.03  cnf(c_0_40, plain, (v1_xboole_0(k1_struct_0(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.82/1.03  fof(c_0_41, plain, ![X30]:(~l1_orders_2(X30)|l1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.82/1.03  fof(c_0_42, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k2_orders_2(X1,k1_struct_0(X1))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t45_orders_2])).
% 0.82/1.03  cnf(c_0_43, plain, (r1_tarski(k1_zfmisc_1(k1_struct_0(X1)),X2)|r1_tarski(k1_xboole_0,X3)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.82/1.03  cnf(c_0_44, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.82/1.03  fof(c_0_45, negated_conjecture, (((((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&v4_orders_2(esk6_0))&v5_orders_2(esk6_0))&l1_orders_2(esk6_0))&k2_orders_2(esk6_0,k1_struct_0(esk6_0))!=u1_struct_0(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_42])])])])).
% 0.82/1.03  cnf(c_0_46, plain, (r1_tarski(k1_zfmisc_1(k1_struct_0(X1)),X2)|r1_tarski(k1_xboole_0,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.82/1.03  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.82/1.03  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_zfmisc_1(k1_struct_0(esk6_0)),X1)|r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.82/1.03  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,X2)|r1_tarski(k1_xboole_0,X3)|~r2_hidden(X1,k1_zfmisc_1(k1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_25, c_0_48])).
% 0.82/1.03  cnf(c_0_50, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))|r2_hidden(X1,X2)|r1_tarski(k1_xboole_0,X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_49, c_0_28])).
% 0.82/1.03  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.82/1.03  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.82/1.03  cnf(c_0_53, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))|r2_hidden(X1,X2)|r1_tarski(k1_xboole_0,X3)|~r1_tarski(X1,k1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.82/1.03  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_22])).
% 0.82/1.03  cnf(c_0_55, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))|r2_hidden(k1_struct_0(esk6_0),X1)|r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.82/1.03  cnf(c_0_56, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.82/1.03  cnf(c_0_57, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))|r1_tarski(k1_xboole_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_18, c_0_55])).
% 0.82/1.03  cnf(c_0_58, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.82/1.03  cnf(c_0_59, plain, (v1_xboole_0(esk2_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_31])).
% 0.82/1.03  cnf(c_0_60, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(k1_struct_0(esk6_0)))|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.82/1.03  cnf(c_0_61, plain, (esk2_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_34, c_0_59])).
% 0.82/1.03  cnf(c_0_62, plain, (r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_31])).
% 0.82/1.03  cnf(c_0_63, negated_conjecture, (k1_zfmisc_1(k1_struct_0(esk6_0))=k1_xboole_0|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_60])).
% 0.82/1.03  cnf(c_0_64, plain, (esk2_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_58])).
% 0.82/1.03  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_xboole_0,k1_struct_0(esk6_0))|r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.82/1.03  cnf(c_0_66, negated_conjecture, (r1_tarski(k1_xboole_0,k1_struct_0(esk6_0))), inference(ef,[status(thm)],[c_0_65])).
% 0.82/1.03  fof(c_0_67, plain, ![X24]:(~l1_struct_0(X24)|k1_struct_0(X24)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).
% 0.82/1.03  fof(c_0_68, plain, ![X31, X32, X33, X35, X36]:((((m1_subset_1(esk4_3(X31,X32,X33),u1_struct_0(X32))|~r2_hidden(X31,a_2_1_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))))&(X31=esk4_3(X31,X32,X33)|~r2_hidden(X31,a_2_1_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))))))&(~m1_subset_1(X35,u1_struct_0(X32))|(~r2_hidden(X35,X33)|r2_orders_2(X32,esk4_3(X31,X32,X33),X35))|~r2_hidden(X31,a_2_1_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))))))&((m1_subset_1(esk5_4(X31,X32,X33,X36),u1_struct_0(X32))|(~m1_subset_1(X36,u1_struct_0(X32))|X31!=X36)|r2_hidden(X31,a_2_1_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))))&((r2_hidden(esk5_4(X31,X32,X33,X36),X33)|(~m1_subset_1(X36,u1_struct_0(X32))|X31!=X36)|r2_hidden(X31,a_2_1_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))))&(~r2_orders_2(X32,X36,esk5_4(X31,X32,X33,X36))|(~m1_subset_1(X36,u1_struct_0(X32))|X31!=X36)|r2_hidden(X31,a_2_1_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.82/1.03  fof(c_0_69, plain, ![X26, X27]:(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|k2_orders_2(X26,X27)=a_2_1_orders_2(X26,X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.82/1.03  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,k1_struct_0(esk6_0))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_66])).
% 0.82/1.03  cnf(c_0_71, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.82/1.03  cnf(c_0_72, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_1_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.82/1.03  cnf(c_0_73, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.82/1.03  cnf(c_0_74, negated_conjecture, (~v1_xboole_0(k1_struct_0(esk6_0))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_70])).
% 0.82/1.03  cnf(c_0_75, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_71, c_0_44])).
% 0.82/1.03  fof(c_0_76, plain, ![X19, X20]:((m1_subset_1(esk3_2(X19,X20),X19)|X19=X20|~m1_subset_1(X20,k1_zfmisc_1(X19)))&(~r2_hidden(esk3_2(X19,X20),X20)|X19=X20|~m1_subset_1(X20,k1_zfmisc_1(X19)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_subset_1])])])])).
% 0.82/1.03  cnf(c_0_77, plain, (v2_struct_0(X1)|r2_hidden(esk5_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_72])).
% 0.82/1.03  fof(c_0_78, plain, ![X28, X29]:(v2_struct_0(X28)|~v3_orders_2(X28)|~v4_orders_2(X28)|~v5_orders_2(X28)|~l1_orders_2(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|m1_subset_1(k2_orders_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).
% 0.82/1.03  cnf(c_0_79, plain, (k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_73, c_0_51])).
% 0.82/1.03  cnf(c_0_80, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_18, c_0_22])).
% 0.82/1.03  cnf(c_0_81, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_58]), c_0_47])])).
% 0.82/1.03  cnf(c_0_82, plain, (X1=X2|~r2_hidden(esk3_2(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.82/1.03  cnf(c_0_83, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_18, c_0_77])).
% 0.82/1.03  cnf(c_0_84, plain, (v2_struct_0(X1)|m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.82/1.03  cnf(c_0_85, plain, (k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.82/1.03  cnf(c_0_86, negated_conjecture, (k2_orders_2(esk6_0,k1_struct_0(esk6_0))!=u1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.82/1.03  cnf(c_0_87, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_81, c_0_22])).
% 0.82/1.03  cnf(c_0_88, plain, (X1=a_2_1_orders_2(X2,X3)|v2_struct_0(X2)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~m1_subset_1(esk3_2(X1,a_2_1_orders_2(X2,X3)),u1_struct_0(X2))|~m1_subset_1(a_2_1_orders_2(X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.82/1.03  cnf(c_0_89, plain, (m1_subset_1(esk3_2(X1,X2),X1)|X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.82/1.03  cnf(c_0_90, plain, (v2_struct_0(X1)|m1_subset_1(a_2_1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.82/1.03  cnf(c_0_91, negated_conjecture, (k2_orders_2(esk6_0,k1_xboole_0)!=u1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_75]), c_0_47])])).
% 0.82/1.03  cnf(c_0_92, negated_conjecture, (k2_orders_2(X1,k1_xboole_0)=a_2_1_orders_2(X1,k1_xboole_0)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_79, c_0_87])).
% 0.82/1.03  cnf(c_0_93, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.82/1.03  cnf(c_0_94, negated_conjecture, (v4_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.82/1.03  cnf(c_0_95, negated_conjecture, (v3_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.82/1.03  cnf(c_0_96, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.82/1.03  cnf(c_0_97, plain, (a_2_1_orders_2(X1,X2)=u1_struct_0(X1)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 0.82/1.03  cnf(c_0_98, negated_conjecture, (a_2_1_orders_2(esk6_0,k1_xboole_0)!=u1_struct_0(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_47]), c_0_93]), c_0_94]), c_0_95])]), c_0_96])).
% 0.82/1.03  cnf(c_0_99, plain, (a_2_1_orders_2(X1,X2)=u1_struct_0(X1)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_51]), c_0_80])).
% 0.82/1.03  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_47]), c_0_93]), c_0_94]), c_0_95]), c_0_58])]), c_0_96]), ['proof']).
% 0.82/1.03  # SZS output end CNFRefutation
% 0.82/1.03  # Proof object total steps             : 101
% 0.82/1.03  # Proof object clause steps            : 71
% 0.82/1.03  # Proof object formula steps           : 30
% 0.82/1.03  # Proof object conjectures             : 27
% 0.82/1.03  # Proof object clause conjectures      : 24
% 0.82/1.03  # Proof object formula conjectures     : 3
% 0.82/1.03  # Proof object initial clauses used    : 26
% 0.82/1.03  # Proof object initial formulas used   : 15
% 0.82/1.03  # Proof object generating inferences   : 43
% 0.82/1.03  # Proof object simplifying inferences  : 24
% 0.82/1.03  # Training examples: 0 positive, 0 negative
% 0.82/1.03  # Parsed axioms                        : 15
% 0.82/1.03  # Removed by relevancy pruning/SinE    : 0
% 0.82/1.03  # Initial clauses                      : 32
% 0.82/1.03  # Removed in clause preprocessing      : 0
% 0.82/1.03  # Initial clauses in saturation        : 32
% 0.82/1.03  # Processed clauses                    : 5526
% 0.82/1.03  # ...of these trivial                  : 21
% 0.82/1.03  # ...subsumed                          : 3984
% 0.82/1.03  # ...remaining for further processing  : 1521
% 0.82/1.03  # Other redundant clauses eliminated   : 3
% 0.82/1.03  # Clauses deleted for lack of memory   : 0
% 0.82/1.03  # Backward-subsumed                    : 288
% 0.82/1.03  # Backward-rewritten                   : 499
% 0.82/1.03  # Generated clauses                    : 45524
% 0.82/1.03  # ...of the previous two non-trivial   : 34049
% 0.82/1.03  # Contextual simplify-reflections      : 94
% 0.82/1.03  # Paramodulations                      : 45510
% 0.82/1.03  # Factorizations                       : 11
% 0.82/1.03  # Equation resolutions                 : 3
% 0.82/1.03  # Propositional unsat checks           : 0
% 0.82/1.03  #    Propositional check models        : 0
% 0.82/1.03  #    Propositional check unsatisfiable : 0
% 0.82/1.03  #    Propositional clauses             : 0
% 0.82/1.03  #    Propositional clauses after purity: 0
% 0.82/1.03  #    Propositional unsat core size     : 0
% 0.82/1.03  #    Propositional preprocessing time  : 0.000
% 0.82/1.03  #    Propositional encoding time       : 0.000
% 0.82/1.03  #    Propositional solver time         : 0.000
% 0.82/1.03  #    Success case prop preproc time    : 0.000
% 0.82/1.03  #    Success case prop encoding time   : 0.000
% 0.82/1.03  #    Success case prop solver time     : 0.000
% 0.82/1.03  # Current number of processed clauses  : 731
% 0.82/1.03  #    Positive orientable unit clauses  : 14
% 0.82/1.03  #    Positive unorientable unit clauses: 0
% 0.82/1.03  #    Negative unit clauses             : 4
% 0.82/1.03  #    Non-unit-clauses                  : 713
% 0.82/1.03  # Current number of unprocessed clauses: 25409
% 0.82/1.03  # ...number of literals in the above   : 177756
% 0.82/1.03  # Current number of archived formulas  : 0
% 0.82/1.03  # Current number of archived clauses   : 787
% 0.82/1.03  # Clause-clause subsumption calls (NU) : 380443
% 0.82/1.03  # Rec. Clause-clause subsumption calls : 71511
% 0.82/1.03  # Non-unit clause-clause subsumptions  : 3433
% 0.82/1.03  # Unit Clause-clause subsumption calls : 749
% 0.82/1.03  # Rewrite failures with RHS unbound    : 0
% 0.82/1.03  # BW rewrite match attempts            : 13
% 0.82/1.03  # BW rewrite match successes           : 9
% 0.82/1.03  # Condensation attempts                : 0
% 0.82/1.03  # Condensation successes               : 0
% 0.82/1.03  # Termbank termtop insertions          : 911259
% 0.82/1.03  
% 0.82/1.03  # -------------------------------------------------
% 0.82/1.03  # User time                : 0.667 s
% 0.82/1.03  # System time              : 0.023 s
% 0.82/1.03  # Total time               : 0.690 s
% 0.82/1.03  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

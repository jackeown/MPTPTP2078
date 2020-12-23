%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1150+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:49 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 125 expanded)
%              Number of clauses        :   36 (  48 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  303 ( 627 expanded)
%              Number of equality atoms :   27 (  68 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(irreflexivity_r2_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ~ r2_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(fraenkel_a_2_0_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X5,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t44_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(d12_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(c_0_14,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ r2_orders_2(X23,X24,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_orders_2])])])).

fof(c_0_15,plain,(
    ! [X13] : m1_subset_1(esk1_1(X13),X13) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_16,plain,(
    ! [X16,X17,X18,X20,X21] :
      ( ( m1_subset_1(esk2_3(X16,X17,X18),u1_struct_0(X17))
        | ~ r2_hidden(X16,a_2_0_orders_2(X17,X18))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17))) )
      & ( X16 = esk2_3(X16,X17,X18)
        | ~ r2_hidden(X16,a_2_0_orders_2(X17,X18))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17))) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X20,X18)
        | r2_orders_2(X17,X20,esk2_3(X16,X17,X18))
        | ~ r2_hidden(X16,a_2_0_orders_2(X17,X18))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17))) )
      & ( m1_subset_1(esk3_4(X16,X17,X18,X21),u1_struct_0(X17))
        | ~ m1_subset_1(X21,u1_struct_0(X17))
        | X16 != X21
        | r2_hidden(X16,a_2_0_orders_2(X17,X18))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17))) )
      & ( r2_hidden(esk3_4(X16,X17,X18,X21),X18)
        | ~ m1_subset_1(X21,u1_struct_0(X17))
        | X16 != X21
        | r2_hidden(X16,a_2_0_orders_2(X17,X18))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17))) )
      & ( ~ r2_orders_2(X17,esk3_4(X16,X17,X18,X21),X21)
        | ~ m1_subset_1(X21,u1_struct_0(X17))
        | X16 != X21
        | r2_hidden(X16,a_2_0_orders_2(X17,X18))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

fof(c_0_17,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | m1_subset_1(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_18,plain,
    ( ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_orders_2(X2,X1,esk2_3(X4,X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_orders_2(X1,X2,esk2_3(X3,X1,X4))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ r2_hidden(esk2_3(X2,X1,X3),X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_21])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,a_2_0_orders_2(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk2_3(X3,X2,X1),X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_31,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( v1_xboole_0(a_2_0_orders_2(X1,u1_struct_0(X1)))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,a_2_0_orders_2(X1,u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_orders_2])).

fof(c_0_37,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v3_orders_2(X8)
      | ~ v4_orders_2(X8)
      | ~ v5_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | k1_orders_2(X8,X9) = a_2_0_orders_2(X8,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_38,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | m1_subset_1(k2_struct_0(X11),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_39,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | l1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_40,plain,(
    ! [X33] :
      ( ~ v1_xboole_0(X33)
      | X33 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(a_2_0_orders_2(X1,u1_struct_0(X1)))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,a_2_0_orders_2(X1,u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & k1_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_36])])])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( v1_xboole_0(a_2_0_orders_2(X1,u1_struct_0(X1)))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_19])).

fof(c_0_48,plain,(
    ! [X10] :
      ( ~ l1_struct_0(X10)
      | k2_struct_0(X10) = u1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_49,negated_conjecture,
    ( k1_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k1_orders_2(X1,k2_struct_0(X1)) = a_2_0_orders_2(X1,k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X15] :
      ( v2_struct_0(X15)
      | ~ l1_struct_0(X15)
      | ~ v1_xboole_0(k2_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_59,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])]),c_0_55])).

cnf(c_0_60,plain,
    ( a_2_0_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0
    | v1_xboole_0(k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_45])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_51]),c_0_52]),c_0_53]),c_0_54])]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_45]),c_0_51])]),
    [proof]).

%------------------------------------------------------------------------------

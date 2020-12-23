%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 127 expanded)
%              Number of clauses        :   37 (  51 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  307 ( 752 expanded)
%              Number of equality atoms :   28 (  74 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   56 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(dt_k1_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

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

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_10,plain,(
    ! [X16,X17,X18] :
      ( ( r1_orders_2(X16,X17,X18)
        | ~ r2_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( X17 != X18
        | ~ r2_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,X17,X18)
        | X17 = X18
        | r2_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_11,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_orders_2])).

cnf(c_0_14,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X24,X25,X26,X28,X29] :
      ( ( m1_subset_1(esk2_3(X24,X25,X26),u1_struct_0(X25))
        | ~ r2_hidden(X24,a_2_0_orders_2(X25,X26))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( X24 = esk2_3(X24,X25,X26)
        | ~ r2_hidden(X24,a_2_0_orders_2(X25,X26))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r2_hidden(X28,X26)
        | r2_orders_2(X25,X28,esk2_3(X24,X25,X26))
        | ~ r2_hidden(X24,a_2_0_orders_2(X25,X26))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( m1_subset_1(esk3_4(X24,X25,X26,X29),u1_struct_0(X25))
        | ~ m1_subset_1(X29,u1_struct_0(X25))
        | X24 != X29
        | r2_hidden(X24,a_2_0_orders_2(X25,X26))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( r2_hidden(esk3_4(X24,X25,X26,X29),X26)
        | ~ m1_subset_1(X29,u1_struct_0(X25))
        | X24 != X29
        | r2_hidden(X24,a_2_0_orders_2(X25,X26))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( ~ r2_orders_2(X25,esk3_4(X24,X25,X26,X29),X29)
        | ~ m1_subset_1(X29,u1_struct_0(X25))
        | X24 != X29
        | r2_hidden(X24,a_2_0_orders_2(X25,X26))
        | v2_struct_0(X25)
        | ~ v3_orders_2(X25)
        | ~ v4_orders_2(X25)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v3_orders_2(X21)
      | ~ v4_orders_2(X21)
      | ~ v5_orders_2(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | m1_subset_1(k1_orders_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & k1_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_20,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | k2_struct_0(X15) = u1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_21,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v3_orders_2(X19)
      | ~ v4_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | k1_orders_2(X19,X20) = a_2_0_orders_2(X19,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

cnf(c_0_27,negated_conjecture,
    ( k1_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X23] :
      ( ~ l1_orders_2(X23)
      | l1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk2_3(X3,X1,X2),X2)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_31,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_orders_2(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( k1_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k1_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_48,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,k1_xboole_0)
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r1_tarski(a_2_0_orders_2(X1,X2),X3)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk1_2(a_2_0_orders_2(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_35])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk1_2(a_2_0_orders_2(X1,X2),X3),u1_struct_0(X1))
    | r1_tarski(a_2_0_orders_2(X1,X2),X3)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_33]),c_0_44]),c_0_45]),c_0_46]),c_0_38])]),c_0_47])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | r1_tarski(a_2_0_orders_2(X1,u1_struct_0(X1)),X2)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_51])])).

cnf(c_0_56,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_44]),c_0_45]),c_0_46]),c_0_38])]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:19:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(t44_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 0.19/0.38  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.19/0.38  fof(dt_k1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 0.19/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.38  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 0.19/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.38  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.38  fof(c_0_10, plain, ![X16, X17, X18]:(((r1_orders_2(X16,X17,X18)|~r2_orders_2(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|~l1_orders_2(X16))&(X17!=X18|~r2_orders_2(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|~l1_orders_2(X16)))&(~r1_orders_2(X16,X17,X18)|X17=X18|r2_orders_2(X16,X17,X18)|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|~l1_orders_2(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  fof(c_0_12, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t44_orders_2])).
% 0.19/0.38  cnf(c_0_14, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_15, plain, ![X24, X25, X26, X28, X29]:((((m1_subset_1(esk2_3(X24,X25,X26),u1_struct_0(X25))|~r2_hidden(X24,a_2_0_orders_2(X25,X26))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))&(X24=esk2_3(X24,X25,X26)|~r2_hidden(X24,a_2_0_orders_2(X25,X26))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))))))&(~m1_subset_1(X28,u1_struct_0(X25))|(~r2_hidden(X28,X26)|r2_orders_2(X25,X28,esk2_3(X24,X25,X26)))|~r2_hidden(X24,a_2_0_orders_2(X25,X26))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))))))&((m1_subset_1(esk3_4(X24,X25,X26,X29),u1_struct_0(X25))|(~m1_subset_1(X29,u1_struct_0(X25))|X24!=X29)|r2_hidden(X24,a_2_0_orders_2(X25,X26))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))&((r2_hidden(esk3_4(X24,X25,X26,X29),X26)|(~m1_subset_1(X29,u1_struct_0(X25))|X24!=X29)|r2_hidden(X24,a_2_0_orders_2(X25,X26))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))&(~r2_orders_2(X25,esk3_4(X24,X25,X26,X29),X29)|(~m1_subset_1(X29,u1_struct_0(X25))|X24!=X29)|r2_hidden(X24,a_2_0_orders_2(X25,X26))|(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.19/0.38  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_18, plain, ![X21, X22]:(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|m1_subset_1(k1_orders_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).
% 0.19/0.38  fof(c_0_19, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&k1_orders_2(esk4_0,k2_struct_0(esk4_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.38  fof(c_0_20, plain, ![X15]:(~l1_struct_0(X15)|k2_struct_0(X15)=u1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.38  cnf(c_0_21, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_22, plain, (r2_orders_2(X2,X1,esk2_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_23, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_26, plain, ![X19, X20]:(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|k1_orders_2(X19,X20)=a_2_0_orders_2(X19,X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (k1_orders_2(esk4_0,k2_struct_0(esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_28, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  fof(c_0_29, plain, ![X23]:(~l1_orders_2(X23)|l1_struct_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.38  cnf(c_0_30, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk2_3(X3,X1,X2),X2)|~r2_hidden(X3,a_2_0_orders_2(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.19/0.38  cnf(c_0_31, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_32, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_orders_2(X1,X3))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_33, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k1_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_37, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_39, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,X2))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_0_orders_2(X1,X3))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k1_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_48, plain, ![X12]:(~r1_tarski(X12,k1_xboole_0)|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.38  cnf(c_0_49, plain, (v2_struct_0(X1)|r1_tarski(a_2_0_orders_2(X1,X2),X3)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk1_2(a_2_0_orders_2(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_39, c_0_35])).
% 0.19/0.38  cnf(c_0_50, plain, (v2_struct_0(X1)|r2_hidden(esk1_2(a_2_0_orders_2(X1,X2),X3),u1_struct_0(X1))|r1_tarski(a_2_0_orders_2(X1,X2),X3)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.19/0.38  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_33]), c_0_44]), c_0_45]), c_0_46]), c_0_38])]), c_0_47])).
% 0.19/0.38  cnf(c_0_53, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.38  cnf(c_0_54, plain, (v2_struct_0(X1)|r1_tarski(a_2_0_orders_2(X1,u1_struct_0(X1)),X2)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_51])])).
% 0.19/0.38  cnf(c_0_56, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_44]), c_0_45]), c_0_46]), c_0_38])]), c_0_47]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 58
% 0.19/0.38  # Proof object clause steps            : 37
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 14
% 0.19/0.38  # Proof object clause conjectures      : 11
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 20
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 15
% 0.19/0.38  # Proof object simplifying inferences  : 20
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 25
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 25
% 0.19/0.38  # Processed clauses                    : 88
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 6
% 0.19/0.38  # ...remaining for further processing  : 82
% 0.19/0.38  # Other redundant clauses eliminated   : 4
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 1
% 0.19/0.38  # Generated clauses                    : 71
% 0.19/0.38  # ...of the previous two non-trivial   : 55
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 67
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 4
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
% 0.19/0.38  # Current number of processed clauses  : 52
% 0.19/0.38  #    Positive orientable unit clauses  : 6
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 42
% 0.19/0.38  # Current number of unprocessed clauses: 14
% 0.19/0.38  # ...number of literals in the above   : 163
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 26
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2878
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 171
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.19/0.38  # Unit Clause-clause subsumption calls : 9
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 13
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5108
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.035 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.040 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

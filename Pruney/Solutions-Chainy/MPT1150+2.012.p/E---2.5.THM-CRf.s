%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:35 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 156 expanded)
%              Number of clauses        :   39 (  64 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  337 ( 864 expanded)
%              Number of equality atoms :   34 (  88 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   56 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t44_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_11,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v3_orders_2(X22)
      | ~ v4_orders_2(X22)
      | ~ v5_orders_2(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | m1_subset_1(k1_orders_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v3_orders_2(X20)
      | ~ v4_orders_2(X20)
      | ~ v5_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | k1_orders_2(X20,X21) = a_2_0_orders_2(X20,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_16,plain,(
    ! [X17,X18,X19] :
      ( ( r1_orders_2(X17,X18,X19)
        | ~ r2_orders_2(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( X18 != X19
        | ~ r2_orders_2(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r1_orders_2(X17,X18,X19)
        | X18 = X19
        | r2_orders_2(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_17,plain,(
    ! [X25,X26,X27,X29,X30] :
      ( ( m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X26))
        | ~ r2_hidden(X25,a_2_0_orders_2(X26,X27))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( X25 = esk3_3(X25,X26,X27)
        | ~ r2_hidden(X25,a_2_0_orders_2(X26,X27))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r2_hidden(X29,X27)
        | r2_orders_2(X26,X29,esk3_3(X25,X26,X27))
        | ~ r2_hidden(X25,a_2_0_orders_2(X26,X27))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( m1_subset_1(esk4_4(X25,X26,X27,X30),u1_struct_0(X26))
        | ~ m1_subset_1(X30,u1_struct_0(X26))
        | X25 != X30
        | r2_hidden(X25,a_2_0_orders_2(X26,X27))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( r2_hidden(esk4_4(X25,X26,X27,X30),X27)
        | ~ m1_subset_1(X30,u1_struct_0(X26))
        | X25 != X30
        | r2_hidden(X25,a_2_0_orders_2(X26,X27))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( ~ r2_orders_2(X26,esk4_4(X25,X26,X27,X30),X30)
        | ~ m1_subset_1(X30,u1_struct_0(X26))
        | X25 != X30
        | r2_hidden(X25,a_2_0_orders_2(X26,X27))
        | v2_struct_0(X26)
        | ~ v3_orders_2(X26)
        | ~ v4_orders_2(X26)
        | ~ v5_orders_2(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | r1_tarski(k1_orders_2(X1,X2),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_orders_2(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_orders_2])).

cnf(c_0_31,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_orders_2(X2,X1,esk3_3(X4,X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( esk3_3(X1,X2,X3) = X1
    | v2_struct_0(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,k1_orders_2(X1,X3))
    | ~ r1_tarski(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_37,plain,
    ( k1_orders_2(X1,u1_struct_0(X1)) = a_2_0_orders_2(X1,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).

fof(c_0_39,plain,(
    ! [X16] :
      ( ~ l1_struct_0(X16)
      | k2_struct_0(X16) = u1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk3_3(X3,X1,X2),X2)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_41,plain,
    ( esk3_3(esk2_1(a_2_0_orders_2(X1,X2)),X1,X2) = esk2_1(a_2_0_orders_2(X1,X2))
    | a_2_0_orders_2(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29])])).

cnf(c_0_43,negated_conjecture,
    ( k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( a_2_0_orders_2(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk2_1(a_2_0_orders_2(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_13]),c_0_35])).

cnf(c_0_46,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | r2_hidden(esk2_1(a_2_0_orders_2(X1,u1_struct_0(X1))),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( k1_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_37]),c_0_48]),c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_55,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_21]),c_0_29])])).

fof(c_0_56,plain,(
    ! [X24] :
      ( ~ l1_orders_2(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_57,negated_conjecture,
    ( ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_48]),c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_58,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:23:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(dt_k1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 0.13/0.40  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.13/0.40  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.13/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.13/0.40  fof(t44_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 0.13/0.40  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.40  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.40  fof(c_0_10, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  fof(c_0_11, plain, ![X22, X23]:(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|m1_subset_1(k1_orders_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).
% 0.13/0.40  fof(c_0_12, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  cnf(c_0_14, plain, (v2_struct_0(X1)|m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  fof(c_0_15, plain, ![X20, X21]:(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|k1_orders_2(X20,X21)=a_2_0_orders_2(X20,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.13/0.40  fof(c_0_16, plain, ![X17, X18, X19]:(((r1_orders_2(X17,X18,X19)|~r2_orders_2(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|~l1_orders_2(X17))&(X18!=X19|~r2_orders_2(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|~l1_orders_2(X17)))&(~r1_orders_2(X17,X18,X19)|X18=X19|r2_orders_2(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|~m1_subset_1(X18,u1_struct_0(X17))|~l1_orders_2(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.13/0.40  fof(c_0_17, plain, ![X25, X26, X27, X29, X30]:((((m1_subset_1(esk3_3(X25,X26,X27),u1_struct_0(X26))|~r2_hidden(X25,a_2_0_orders_2(X26,X27))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))&(X25=esk3_3(X25,X26,X27)|~r2_hidden(X25,a_2_0_orders_2(X26,X27))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))))))&(~m1_subset_1(X29,u1_struct_0(X26))|(~r2_hidden(X29,X27)|r2_orders_2(X26,X29,esk3_3(X25,X26,X27)))|~r2_hidden(X25,a_2_0_orders_2(X26,X27))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))))))&((m1_subset_1(esk4_4(X25,X26,X27,X30),u1_struct_0(X26))|(~m1_subset_1(X30,u1_struct_0(X26))|X25!=X30)|r2_hidden(X25,a_2_0_orders_2(X26,X27))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))&((r2_hidden(esk4_4(X25,X26,X27,X30),X27)|(~m1_subset_1(X30,u1_struct_0(X26))|X25!=X30)|r2_hidden(X25,a_2_0_orders_2(X26,X27))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))&(~r2_orders_2(X26,esk4_4(X25,X26,X27,X30),X30)|(~m1_subset_1(X30,u1_struct_0(X26))|X25!=X30)|r2_hidden(X25,a_2_0_orders_2(X26,X27))|(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.13/0.40  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_19, plain, (v2_struct_0(X1)|r1_tarski(k1_orders_2(X1,X2),u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.40  cnf(c_0_20, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.40  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_24, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_25, plain, (X1=esk3_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  fof(c_0_26, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.13/0.40  cnf(c_0_27, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_orders_2(X1,X3))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.40  cnf(c_0_28, plain, (k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.40  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.40  fof(c_0_30, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t44_orders_2])).
% 0.13/0.40  cnf(c_0_31, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_32, plain, (r2_orders_2(X2,X1,esk3_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_33, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_34, plain, (esk3_3(X1,X2,X3)=X1|v2_struct_0(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~l1_orders_2(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~r1_tarski(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.13/0.40  cnf(c_0_35, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_36, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X2,k1_orders_2(X1,X3))|~r1_tarski(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_27, c_0_21])).
% 0.13/0.40  cnf(c_0_37, plain, (k1_orders_2(X1,u1_struct_0(X1))=a_2_0_orders_2(X1,u1_struct_0(X1))|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.40  fof(c_0_38, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).
% 0.13/0.40  fof(c_0_39, plain, ![X16]:(~l1_struct_0(X16)|k2_struct_0(X16)=u1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.40  cnf(c_0_40, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk3_3(X3,X1,X2),X2)|~r2_hidden(X3,a_2_0_orders_2(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.13/0.40  cnf(c_0_41, plain, (esk3_3(esk2_1(a_2_0_orders_2(X1,X2)),X1,X2)=esk2_1(a_2_0_orders_2(X1,X2))|a_2_0_orders_2(X1,X2)=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.40  cnf(c_0_42, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X2,a_2_0_orders_2(X1,u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29])])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_44, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.40  cnf(c_0_45, plain, (a_2_0_orders_2(X1,X2)=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk2_1(a_2_0_orders_2(X1,X2)),X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_13]), c_0_35])).
% 0.13/0.40  cnf(c_0_46, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|r2_hidden(esk2_1(a_2_0_orders_2(X1,u1_struct_0(X1))),u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_42, c_0_35])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (k1_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_53, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_37]), c_0_48]), c_0_49]), c_0_50]), c_0_51])]), c_0_52])).
% 0.13/0.40  cnf(c_0_55, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_21]), c_0_29])])).
% 0.13/0.40  fof(c_0_56, plain, ![X24]:(~l1_orders_2(X24)|l1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_48]), c_0_49]), c_0_50]), c_0_51])]), c_0_52])).
% 0.13/0.40  cnf(c_0_58, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_51])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 60
% 0.13/0.40  # Proof object clause steps            : 39
% 0.13/0.40  # Proof object formula steps           : 21
% 0.13/0.40  # Proof object conjectures             : 13
% 0.13/0.40  # Proof object clause conjectures      : 10
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 20
% 0.13/0.40  # Proof object initial formulas used   : 10
% 0.13/0.40  # Proof object generating inferences   : 18
% 0.13/0.40  # Proof object simplifying inferences  : 22
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 10
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 25
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 25
% 0.13/0.40  # Processed clauses                    : 143
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 49
% 0.13/0.40  # ...remaining for further processing  : 94
% 0.13/0.40  # Other redundant clauses eliminated   : 4
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 4
% 0.13/0.40  # Backward-rewritten                   : 0
% 0.13/0.40  # Generated clauses                    : 361
% 0.13/0.40  # ...of the previous two non-trivial   : 357
% 0.13/0.40  # Contextual simplify-reflections      : 14
% 0.13/0.40  # Paramodulations                      : 357
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 4
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 86
% 0.13/0.40  #    Positive orientable unit clauses  : 5
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 78
% 0.13/0.40  # Current number of unprocessed clauses: 238
% 0.13/0.40  # ...number of literals in the above   : 2176
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 4
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 5254
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 195
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 67
% 0.13/0.40  # Unit Clause-clause subsumption calls : 48
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 2
% 0.13/0.40  # BW rewrite match successes           : 0
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 15219
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.047 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.052 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

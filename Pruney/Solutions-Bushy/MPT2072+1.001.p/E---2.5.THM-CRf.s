%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2072+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:12 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   92 (1156 expanded)
%              Number of clauses        :   65 ( 445 expanded)
%              Number of leaves         :   13 ( 291 expanded)
%              Depth                    :   19
%              Number of atoms          :  382 (6702 expanded)
%              Number of equality atoms :   51 ( 528 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   65 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_cantor_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k2_cantor_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> ? [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(X1)))
                      & r1_tarski(X5,X2)
                      & v1_finset_1(X5)
                      & X4 = k8_setfam_1(X1,X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_cantor_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k2_cantor_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k2_cantor_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_cantor_1)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(t32_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
           => v2_tops_2(k2_cantor_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_yellow19)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t44_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_pre_topc)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_13,plain,(
    ! [X13,X14,X15,X16,X18,X20] :
      ( ( m1_subset_1(esk2_4(X13,X14,X15,X16),k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( r1_tarski(esk2_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( v1_finset_1(esk2_4(X13,X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( X16 = k8_setfam_1(X13,esk2_4(X13,X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ r1_tarski(X18,X14)
        | ~ v1_finset_1(X18)
        | X16 != k8_setfam_1(X13,X18)
        | r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | X15 != k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( m1_subset_1(esk3_3(X13,X14,X15),k1_zfmisc_1(X13))
        | X15 = k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( ~ r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ r1_tarski(X20,X14)
        | ~ v1_finset_1(X20)
        | esk3_3(X13,X14,X15) != k8_setfam_1(X13,X20)
        | X15 = k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(k1_zfmisc_1(X13)))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | X15 = k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( r1_tarski(esk4_3(X13,X14,X15),X14)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | X15 = k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | X15 = k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( esk3_3(X13,X14,X15) = k8_setfam_1(X13,esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | X15 = k2_cantor_1(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_cantor_1])])])])])).

fof(c_0_14,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | m1_subset_1(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))
      | m1_subset_1(k2_cantor_1(X22,X23),k1_zfmisc_1(k1_zfmisc_1(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_cantor_1])])).

fof(c_0_16,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_tops_2(X9,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r2_hidden(X10,X9)
        | v4_pre_topc(X10,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | v2_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | v2_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ l1_pre_topc(X8) )
      & ( ~ v4_pre_topc(esk1_2(X8,X9),X8)
        | v2_tops_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | X3 != k2_cantor_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(k2_cantor_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v2_tops_2(X2,X1)
             => v2_tops_2(k2_cantor_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_yellow19])).

fof(c_0_21,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,plain,
    ( r1_tarski(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | X3 != k2_cantor_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk2_4(X1,X2,k2_cantor_1(X1,X2),X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X3,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_17,c_0_18])]),c_0_19])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
    & v2_tops_2(esk7_0,esk6_0)
    & ~ v2_tops_2(k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(esk2_4(X1,X2,k2_cantor_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_22,c_0_18])]),c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,esk2_4(u1_struct_0(X1),X2,k2_cantor_1(u1_struct_0(X1),X2),X3)),esk2_4(u1_struct_0(X1),X2,k2_cantor_1(u1_struct_0(X1),X2),X3))
    | v2_tops_2(esk2_4(u1_struct_0(X1),X2,k2_cantor_1(u1_struct_0(X1),X2),X3),X1)
    | ~ r2_hidden(X3,k2_cantor_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,k2_cantor_1(u1_struct_0(X1),X2)),k2_cantor_1(u1_struct_0(X1),X2))
    | v2_tops_2(k2_cantor_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_34,plain,(
    ! [X30,X31] :
      ( ( m1_subset_1(esk5_2(X30,X31),k1_zfmisc_1(u1_struct_0(X30)))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X30),X31),X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(esk5_2(X30,X31),X31)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X30),X31),X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ v4_pre_topc(esk5_2(X30,X31),X30)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X30),X31),X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X30))))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_pre_topc])])])])])).

cnf(c_0_35,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk2_4(X1,X2,k2_cantor_1(X1,X2),X3),k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1)),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1))
    | v2_tops_2(esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1),esk6_0)
    | ~ r2_hidden(X1,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)),k2_cantor_1(u1_struct_0(esk6_0),esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X6,X7] :
      ( ( X7 = k1_xboole_0
        | k8_setfam_1(X6,X7) = k6_setfam_1(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) )
      & ( X7 != k1_xboole_0
        | k8_setfam_1(X6,X7) = X6
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_41,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( v4_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v2_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( v2_tops_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_45,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,esk2_4(X3,X2,k2_cantor_1(X3,X2),X4))
    | ~ r2_hidden(X4,k2_cantor_1(X3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))))
    | v2_tops_2(esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk2_4(X3,X1,k2_cantor_1(X3,X1),X4))
    | ~ r2_hidden(X4,k2_cantor_1(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),esk2_4(u1_struct_0(X1),X2,k2_cantor_1(u1_struct_0(X1),X2),X3)),X1)
    | r2_hidden(esk5_2(X1,esk2_4(u1_struct_0(X1),X2,k2_cantor_1(u1_struct_0(X1),X2),X3)),esk2_4(u1_struct_0(X1),X2,k2_cantor_1(u1_struct_0(X1),X2),X3))
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X3,k2_cantor_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,plain,
    ( v2_tops_2(esk2_4(u1_struct_0(X1),X2,k2_cantor_1(u1_struct_0(X1),X2),X3),X1)
    | ~ v4_pre_topc(esk1_2(X1,esk2_4(u1_struct_0(X1),X2,k2_cantor_1(u1_struct_0(X1),X2),X3)),X1)
    | ~ r2_hidden(X3,k2_cantor_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( v4_pre_topc(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_29]),c_0_44]),c_0_30])])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( v2_tops_2(esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))),esk6_0)
    | m1_subset_1(esk1_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_38]),c_0_29])])).

cnf(c_0_56,negated_conjecture,
    ( v2_tops_2(esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))),esk6_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_38]),c_0_29])])).

cnf(c_0_57,plain,
    ( k6_setfam_1(X1,esk2_4(X1,X2,k2_cantor_1(X1,X2),X3)) = k8_setfam_1(X1,esk2_4(X1,X2,k2_cantor_1(X1,X2),X3))
    | esk2_4(X1,X2,k2_cantor_1(X1,X2),X3) = k1_xboole_0
    | ~ r2_hidden(X3,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1)),esk6_0)
    | r2_hidden(esk5_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1)),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1))
    | ~ r2_hidden(X1,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_29]),c_0_51]),c_0_30])])).

cnf(c_0_59,negated_conjecture,
    ( v2_tops_2(esk2_4(u1_struct_0(esk6_0),X1,k2_cantor_1(u1_struct_0(esk6_0),X1),X2),esk6_0)
    | ~ r2_hidden(esk1_2(esk6_0,esk2_4(u1_struct_0(esk6_0),X1,k2_cantor_1(u1_struct_0(esk6_0),X1),X2)),esk7_0)
    | ~ r2_hidden(X2,k2_cantor_1(u1_struct_0(esk6_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_30])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk7_0)
    | v2_tops_2(esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1)) = k8_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1))
    | esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),X1) = k1_xboole_0
    | ~ r2_hidden(X1,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_29])).

cnf(c_0_62,plain,
    ( v4_pre_topc(X1,X2)
    | ~ r2_hidden(X1,esk2_4(u1_struct_0(X2),X3,k2_cantor_1(u1_struct_0(X2),X3),X4))
    | ~ r2_hidden(X4,k2_cantor_1(u1_struct_0(X2),X3))
    | ~ v2_tops_2(esk2_4(u1_struct_0(X2),X3,k2_cantor_1(u1_struct_0(X2),X3),X4),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0)
    | r2_hidden(esk5_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( v2_tops_2(esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_38]),c_0_29])])).

cnf(c_0_65,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(esk5_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))) = k8_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))))
    | esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_67,negated_conjecture,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0)
    | v4_pre_topc(esk5_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_38]),c_0_64]),c_0_30]),c_0_29])])).

cnf(c_0_68,negated_conjecture,
    ( esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))) = k1_xboole_0
    | v4_pre_topc(k8_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0)
    | ~ v4_pre_topc(esk5_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0)
    | ~ m1_subset_1(esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_51]),c_0_30])])).

cnf(c_0_69,negated_conjecture,
    ( esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))) = k1_xboole_0
    | v4_pre_topc(k8_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0)
    | v4_pre_topc(esk5_2(esk6_0,esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))) = k1_xboole_0
    | v4_pre_topc(k8_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0)
    | ~ m1_subset_1(esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_71,plain,
    ( X1 = k8_setfam_1(X2,esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | X4 != k2_cantor_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))) = k1_xboole_0
    | v4_pre_topc(k8_setfam_1(u1_struct_0(esk6_0),esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)))),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_24]),c_0_38]),c_0_29])])).

cnf(c_0_73,plain,
    ( k8_setfam_1(X1,esk2_4(X1,X2,k2_cantor_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_cantor_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_71,c_0_18])]),c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( esk2_4(u1_struct_0(esk6_0),esk7_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0),esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0))) = k1_xboole_0
    | v4_pre_topc(esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_38]),c_0_29])])).

cnf(c_0_75,plain,
    ( v2_tops_2(k2_cantor_1(u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(esk1_2(X1,k2_cantor_1(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_19])).

cnf(c_0_76,negated_conjecture,
    ( esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)) = k8_setfam_1(u1_struct_0(esk6_0),k1_xboole_0)
    | v4_pre_topc(esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_38]),c_0_29])])).

cnf(c_0_77,negated_conjecture,
    ( esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)) = k8_setfam_1(u1_struct_0(esk6_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_30]),c_0_29])]),c_0_32])).

cnf(c_0_78,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_79,negated_conjecture,
    ( v4_pre_topc(esk1_2(esk6_0,k2_cantor_1(u1_struct_0(esk6_0),esk7_0)),esk6_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_74]),c_0_38]),c_0_29])])).

fof(c_0_80,plain,(
    ! [X25] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v4_pre_topc(k2_struct_0(X25),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

fof(c_0_81,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | k2_struct_0(X12) = u1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_82,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v4_pre_topc(k8_setfam_1(u1_struct_0(esk6_0),k1_xboole_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_77]),c_0_30]),c_0_29])]),c_0_32])).

cnf(c_0_84,plain,
    ( k8_setfam_1(X1,k1_xboole_0) = X1
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_79]),c_0_30]),c_0_29])]),c_0_32])).

cnf(c_0_86,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_88,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( ~ v4_pre_topc(u1_struct_0(esk6_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])])).

cnf(c_0_90,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_51]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------

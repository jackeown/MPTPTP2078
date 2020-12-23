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
% DateTime   : Thu Dec  3 11:15:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  76 expanded)
%              Number of clauses        :   25 (  32 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  218 ( 414 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | r1_tarski(X10,k3_tarski(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | m1_subset_1(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_13,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | m1_subset_1(u1_pre_topc(X27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X12,X13] :
      ( ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(k3_tarski(X12),X13) )
      & ( ~ r1_tarski(esk2_2(X12,X13),X13)
        | r1_tarski(k3_tarski(X12),X13) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_tarski(X1) = X2
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r1_tarski(X21,u1_pre_topc(X20))
        | r2_hidden(k5_setfam_1(u1_struct_0(X20),X21),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X22,u1_pre_topc(X20))
        | ~ r2_hidden(X23,u1_pre_topc(X20))
        | r2_hidden(k9_subset_1(u1_struct_0(X20),X22,X23),u1_pre_topc(X20))
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk5_1(X20),u1_pre_topc(X20))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))
        | m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk5_1(X20),u1_pre_topc(X20))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))
        | r1_tarski(esk3_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk4_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk5_1(X20),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))
        | ~ r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))
        | v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k3_tarski(X1) = X2
    | r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0))) != u1_struct_0(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | r2_hidden(esk2_2(u1_pre_topc(X1),u1_struct_0(X1)),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_34,plain,(
    ! [X28] :
      ( v1_xboole_0(X28)
      | ~ r2_hidden(k3_tarski(X28),X28)
      | k4_yellow_0(k2_yellow_1(X28)) = k3_tarski(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_35,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_tarski(X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(X2)),u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk6_0)) = u1_struct_0(esk6_0)
    | r2_hidden(esk2_2(u1_pre_topc(esk6_0),u1_struct_0(esk6_0)),u1_pre_topc(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk6_0)) = u1_struct_0(esk6_0)
    | r1_tarski(k3_tarski(u1_pre_topc(esk6_0)),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_33])])).

cnf(c_0_41,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk6_0)) = u1_struct_0(esk6_0)
    | ~ r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0))) != u1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:13:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.38  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.38  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.19/0.38  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.19/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.38  fof(c_0_10, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X10, X11]:(~r2_hidden(X10,X11)|r1_tarski(X10,k3_tarski(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.19/0.38  fof(c_0_12, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|m1_subset_1(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  fof(c_0_13, plain, ![X27]:(~l1_pre_topc(X27)|m1_subset_1(u1_pre_topc(X27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.38  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_15, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  fof(c_0_16, plain, ![X12, X13]:((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(k3_tarski(X12),X13))&(~r1_tarski(esk2_2(X12,X13),X13)|r1_tarski(k3_tarski(X12),X13))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.19/0.38  fof(c_0_17, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_18, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_19, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_20, plain, (k3_tarski(X1)=X2|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_21, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_22, plain, ![X20, X21, X22, X23]:((((r2_hidden(u1_struct_0(X20),u1_pre_topc(X20))|~v2_pre_topc(X20)|~l1_pre_topc(X20))&(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|(~r1_tarski(X21,u1_pre_topc(X20))|r2_hidden(k5_setfam_1(u1_struct_0(X20),X21),u1_pre_topc(X20)))|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(X22,u1_pre_topc(X20))|~r2_hidden(X23,u1_pre_topc(X20))|r2_hidden(k9_subset_1(u1_struct_0(X20),X22,X23),u1_pre_topc(X20))))|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk5_1(X20),u1_pre_topc(X20))|(m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))|(m1_subset_1(esk3_1(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))&(((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(r1_tarski(esk3_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(r1_tarski(esk3_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(r1_tarski(esk3_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk5_1(X20),u1_pre_topc(X20))|(r1_tarski(esk3_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))|(r1_tarski(esk3_1(X20),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))&((m1_subset_1(esk4_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&((m1_subset_1(esk5_1(X20),k1_zfmisc_1(u1_struct_0(X20)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(((r2_hidden(esk4_1(X20),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20))&(r2_hidden(esk5_1(X20),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r2_hidden(k9_subset_1(u1_struct_0(X20),esk4_1(X20),esk5_1(X20)),u1_pre_topc(X20))|(~r2_hidden(k5_setfam_1(u1_struct_0(X20),esk3_1(X20)),u1_pre_topc(X20))|~r2_hidden(u1_struct_0(X20),u1_pre_topc(X20)))|v2_pre_topc(X20)|~l1_pre_topc(X20)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.38  fof(c_0_23, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.19/0.38  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.38  cnf(c_0_26, plain, (k3_tarski(X1)=X2|r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_27, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  fof(c_0_28, negated_conjecture, (((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0)))!=u1_struct_0(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.19/0.38  cnf(c_0_29, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_30, plain, (r1_tarski(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_31, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|r2_hidden(esk2_2(u1_pre_topc(X1),u1_struct_0(X1)),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  fof(c_0_34, plain, ![X28]:(v1_xboole_0(X28)|(~r2_hidden(k3_tarski(X28),X28)|k4_yellow_0(k2_yellow_1(X28))=k3_tarski(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.19/0.38  fof(c_0_35, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.38  cnf(c_0_36, plain, (r1_tarski(k3_tarski(X1),u1_struct_0(X2))|~l1_pre_topc(X2)|~r2_hidden(esk2_2(X1,u1_struct_0(X2)),u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (k3_tarski(u1_pre_topc(esk6_0))=u1_struct_0(esk6_0)|r2_hidden(esk2_2(u1_pre_topc(esk6_0),u1_struct_0(esk6_0)),u1_pre_topc(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.19/0.38  cnf(c_0_38, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_39, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k3_tarski(u1_pre_topc(esk6_0))=u1_struct_0(esk6_0)|r1_tarski(k3_tarski(u1_pre_topc(esk6_0)),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_33])])).
% 0.19/0.38  cnf(c_0_41, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (k3_tarski(u1_pre_topc(esk6_0))=u1_struct_0(esk6_0)|~r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))), inference(spm,[status(thm)],[c_0_20, c_0_40])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0)))!=u1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (~r2_hidden(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_32]), c_0_33])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 46
% 0.19/0.38  # Proof object clause steps            : 25
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 11
% 0.19/0.38  # Proof object clause conjectures      : 8
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 13
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 9
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 35
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 35
% 0.19/0.38  # Processed clauses                    : 173
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 38
% 0.19/0.38  # ...remaining for further processing  : 135
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 183
% 0.19/0.38  # ...of the previous two non-trivial   : 162
% 0.19/0.38  # Contextual simplify-reflections      : 3
% 0.19/0.38  # Paramodulations                      : 181
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
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
% 0.19/0.38  # Current number of processed clauses  : 99
% 0.19/0.38  #    Positive orientable unit clauses  : 4
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 92
% 0.19/0.38  # Current number of unprocessed clauses: 58
% 0.19/0.38  # ...number of literals in the above   : 213
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 34
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2033
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 622
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 41
% 0.19/0.38  # Unit Clause-clause subsumption calls : 9
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6561
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.039 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

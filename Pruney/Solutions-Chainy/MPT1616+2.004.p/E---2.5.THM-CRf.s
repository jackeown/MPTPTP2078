%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:56 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of clauses        :   30 (  32 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  234 ( 395 expanded)
%              Number of equality atoms :   30 (  45 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

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

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | r1_tarski(X17,k3_tarski(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | r1_tarski(k3_tarski(X19),k3_tarski(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X21] : k3_tarski(k1_zfmisc_1(X21)) = X21 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_tarski(X1) = X2
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_28,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X22,X23)
      | v1_xboole_0(X23)
      | r2_hidden(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_29,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | m1_subset_1(u1_pre_topc(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_30,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k3_tarski(X1) = X2
    | ~ r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X32] :
      ( v1_xboole_0(X32)
      | ~ r2_hidden(k3_tarski(X32),X32)
      | k4_yellow_0(k2_yellow_1(X32)) = k3_tarski(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_38,plain,
    ( k3_tarski(X1) = X2
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

fof(c_0_40,plain,(
    ! [X24,X25,X26,X27] :
      ( ( r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ r1_tarski(X25,u1_pre_topc(X24))
        | r2_hidden(k5_setfam_1(u1_struct_0(X24),X25),u1_pre_topc(X24))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r2_hidden(X26,u1_pre_topc(X24))
        | ~ r2_hidden(X27,u1_pre_topc(X24))
        | r2_hidden(k9_subset_1(u1_struct_0(X24),X26,X27),u1_pre_topc(X24))
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))
        | m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))
        | m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(esk4_1(X24),u1_pre_topc(X24))
        | m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(esk5_1(X24),u1_pre_topc(X24))
        | m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))
        | m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))
        | r1_tarski(esk3_1(X24),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))
        | r1_tarski(esk3_1(X24),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(esk4_1(X24),u1_pre_topc(X24))
        | r1_tarski(esk3_1(X24),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(esk5_1(X24),u1_pre_topc(X24))
        | r1_tarski(esk3_1(X24),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))
        | r1_tarski(esk3_1(X24),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(esk4_1(X24),u1_pre_topc(X24))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( r2_hidden(esk5_1(X24),u1_pre_topc(X24))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))
        | ~ r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))
        | v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0))) != u1_struct_0(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_41])])])])).

cnf(c_0_46,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_47,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0))) != u1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:16:49 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.33  # No SInE strategy applied
% 0.14/0.33  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.052 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.40  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.14/0.40  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.14/0.40  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.14/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.40  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.14/0.40  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.14/0.40  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.14/0.40  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.14/0.40  fof(c_0_11, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|~r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.40  fof(c_0_12, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.40  fof(c_0_13, plain, ![X17, X18]:(~r2_hidden(X17,X18)|r1_tarski(X17,k3_tarski(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.14/0.40  fof(c_0_14, plain, ![X19, X20]:(~r1_tarski(X19,X20)|r1_tarski(k3_tarski(X19),k3_tarski(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.14/0.40  fof(c_0_15, plain, ![X21]:k3_tarski(k1_zfmisc_1(X21))=X21, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.14/0.40  cnf(c_0_16, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_18, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_19, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_20, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_21, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  fof(c_0_22, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.40  cnf(c_0_23, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 0.14/0.40  cnf(c_0_24, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_25, plain, (k3_tarski(X1)=X2|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.40  cnf(c_0_26, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  fof(c_0_28, plain, ![X22, X23]:(~m1_subset_1(X22,X23)|(v1_xboole_0(X23)|r2_hidden(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.40  fof(c_0_29, plain, ![X31]:(~l1_pre_topc(X31)|m1_subset_1(u1_pre_topc(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.14/0.40  cnf(c_0_30, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  cnf(c_0_31, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.40  cnf(c_0_32, plain, (k3_tarski(X1)=X2|~r1_tarski(X1,k1_zfmisc_1(X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.40  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_27])).
% 0.14/0.40  cnf(c_0_34, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.40  cnf(c_0_35, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.40  cnf(c_0_36, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.40  fof(c_0_37, plain, ![X32]:(v1_xboole_0(X32)|(~r2_hidden(k3_tarski(X32),X32)|k4_yellow_0(k2_yellow_1(X32))=k3_tarski(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.14/0.40  cnf(c_0_38, plain, (k3_tarski(X1)=X2|~r2_hidden(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.40  cnf(c_0_39, plain, (r2_hidden(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.14/0.40  fof(c_0_40, plain, ![X24, X25, X26, X27]:((((r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))|~v2_pre_topc(X24)|~l1_pre_topc(X24))&(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|(~r1_tarski(X25,u1_pre_topc(X24))|r2_hidden(k5_setfam_1(u1_struct_0(X24),X25),u1_pre_topc(X24)))|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|(~r2_hidden(X26,u1_pre_topc(X24))|~r2_hidden(X27,u1_pre_topc(X24))|r2_hidden(k9_subset_1(u1_struct_0(X24),X26,X27),u1_pre_topc(X24))))|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(((m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&((m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(((r2_hidden(esk4_1(X24),u1_pre_topc(X24))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(r2_hidden(esk5_1(X24),u1_pre_topc(X24))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))))&(((m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&((m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(((r2_hidden(esk4_1(X24),u1_pre_topc(X24))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(r2_hidden(esk5_1(X24),u1_pre_topc(X24))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))))&((m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&((m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(((r2_hidden(esk4_1(X24),u1_pre_topc(X24))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(r2_hidden(esk5_1(X24),u1_pre_topc(X24))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.14/0.40  fof(c_0_41, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.14/0.40  cnf(c_0_42, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.40  cnf(c_0_43, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.40  cnf(c_0_44, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.40  fof(c_0_45, negated_conjecture, (((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0)))!=u1_struct_0(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_41])])])])).
% 0.14/0.40  cnf(c_0_46, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_42, c_0_30])).
% 0.14/0.40  cnf(c_0_47, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.14/0.40  cnf(c_0_48, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0)))!=u1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.40  cnf(c_0_49, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_44])).
% 0.14/0.40  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.40  cnf(c_0_51, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.40  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 53
% 0.14/0.40  # Proof object clause steps            : 30
% 0.14/0.40  # Proof object formula steps           : 23
% 0.14/0.40  # Proof object conjectures             : 7
% 0.14/0.40  # Proof object clause conjectures      : 4
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 15
% 0.14/0.40  # Proof object initial formulas used   : 11
% 0.14/0.40  # Proof object generating inferences   : 11
% 0.14/0.40  # Proof object simplifying inferences  : 9
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 11
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 37
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 37
% 0.14/0.40  # Processed clauses                    : 155
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 28
% 0.14/0.40  # ...remaining for further processing  : 127
% 0.14/0.40  # Other redundant clauses eliminated   : 4
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 0
% 0.14/0.40  # Backward-rewritten                   : 0
% 0.14/0.40  # Generated clauses                    : 187
% 0.14/0.40  # ...of the previous two non-trivial   : 157
% 0.14/0.40  # Contextual simplify-reflections      : 2
% 0.14/0.40  # Paramodulations                      : 183
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 4
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 87
% 0.14/0.40  #    Positive orientable unit clauses  : 6
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 3
% 0.14/0.40  #    Non-unit-clauses                  : 78
% 0.14/0.40  # Current number of unprocessed clauses: 75
% 0.14/0.40  # ...number of literals in the above   : 280
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 36
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 822
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 247
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 25
% 0.14/0.40  # Unit Clause-clause subsumption calls : 5
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 1
% 0.14/0.40  # BW rewrite match successes           : 0
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 6512
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.065 s
% 0.19/0.40  # System time              : 0.006 s
% 0.19/0.40  # Total time               : 0.071 s
% 0.19/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:57 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 (  75 expanded)
%              Number of clauses        :   30 (  34 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :  249 ( 407 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X21,X20)
        | r2_hidden(X21,X20)
        | v1_xboole_0(X20) )
      & ( ~ r2_hidden(X21,X20)
        | m1_subset_1(X21,X20)
        | v1_xboole_0(X20) )
      & ( ~ m1_subset_1(X21,X20)
        | v1_xboole_0(X21)
        | ~ v1_xboole_0(X20) )
      & ( ~ v1_xboole_0(X21)
        | m1_subset_1(X21,X20)
        | ~ v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_17,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | r1_tarski(k3_tarski(X17),k3_tarski(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_19,plain,(
    ! [X19] : k3_tarski(k1_zfmisc_1(X19)) = X19 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X16] : r1_tarski(X16,k1_zfmisc_1(k3_tarski(X16))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k3_tarski(X1) = X2
    | ~ r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X2,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( k3_tarski(X1) = X2
    | ~ r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_38,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | m1_subset_1(u1_pre_topc(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_39,plain,(
    ! [X32] :
      ( v1_xboole_0(X32)
      | ~ r2_hidden(k3_tarski(X32),X32)
      | k4_yellow_0(k2_yellow_1(X32)) = k3_tarski(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_40,plain,
    ( k3_tarski(X1) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_41,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_42,plain,(
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

fof(c_0_43,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0))) != u1_struct_0(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_43])])])])).

cnf(c_0_48,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_44,c_0_22])).

cnf(c_0_49,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0))) != u1_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:06:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.030 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.39  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.19/0.39  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.19/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.39  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.19/0.39  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.39  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.19/0.39  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.39  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.19/0.39  fof(c_0_12, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.39  fof(c_0_13, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.39  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  fof(c_0_16, plain, ![X20, X21]:(((~m1_subset_1(X21,X20)|r2_hidden(X21,X20)|v1_xboole_0(X20))&(~r2_hidden(X21,X20)|m1_subset_1(X21,X20)|v1_xboole_0(X20)))&((~m1_subset_1(X21,X20)|v1_xboole_0(X21)|~v1_xboole_0(X20))&(~v1_xboole_0(X21)|m1_subset_1(X21,X20)|~v1_xboole_0(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.39  fof(c_0_17, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_18, plain, ![X17, X18]:(~r1_tarski(X17,X18)|r1_tarski(k3_tarski(X17),k3_tarski(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.19/0.39  fof(c_0_19, plain, ![X19]:k3_tarski(k1_zfmisc_1(X19))=X19, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.19/0.39  cnf(c_0_20, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.39  cnf(c_0_21, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_22, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_23, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_24, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_25, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.19/0.39  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.39  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_28, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.39  fof(c_0_29, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.39  fof(c_0_30, plain, ![X16]:r1_tarski(X16,k1_zfmisc_1(k3_tarski(X16))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.19/0.39  cnf(c_0_31, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  cnf(c_0_32, plain, (m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.39  cnf(c_0_33, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_34, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_35, plain, (k3_tarski(X1)=X2|~r1_tarski(X1,k1_zfmisc_1(X2))|~r2_hidden(X2,k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.39  cnf(c_0_36, plain, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(X2)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.39  cnf(c_0_37, plain, (k3_tarski(X1)=X2|~r1_tarski(X1,k1_zfmisc_1(X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.39  fof(c_0_38, plain, ![X31]:(~l1_pre_topc(X31)|m1_subset_1(u1_pre_topc(X31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.39  fof(c_0_39, plain, ![X32]:(v1_xboole_0(X32)|(~r2_hidden(k3_tarski(X32),X32)|k4_yellow_0(k2_yellow_1(X32))=k3_tarski(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.19/0.39  cnf(c_0_40, plain, (k3_tarski(X1)=X2|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_15])).
% 0.19/0.39  cnf(c_0_41, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.39  fof(c_0_42, plain, ![X24, X25, X26, X27]:((((r2_hidden(u1_struct_0(X24),u1_pre_topc(X24))|~v2_pre_topc(X24)|~l1_pre_topc(X24))&(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|(~r1_tarski(X25,u1_pre_topc(X24))|r2_hidden(k5_setfam_1(u1_struct_0(X24),X25),u1_pre_topc(X24)))|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X24)))|(~r2_hidden(X26,u1_pre_topc(X24))|~r2_hidden(X27,u1_pre_topc(X24))|r2_hidden(k9_subset_1(u1_struct_0(X24),X26,X27),u1_pre_topc(X24))))|~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(((m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&((m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(((r2_hidden(esk4_1(X24),u1_pre_topc(X24))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(r2_hidden(esk5_1(X24),u1_pre_topc(X24))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))|(m1_subset_1(esk3_1(X24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X24))))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))))&(((m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&((m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(((r2_hidden(esk4_1(X24),u1_pre_topc(X24))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(r2_hidden(esk5_1(X24),u1_pre_topc(X24))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))|(r1_tarski(esk3_1(X24),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))))&((m1_subset_1(esk4_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&((m1_subset_1(esk5_1(X24),k1_zfmisc_1(u1_struct_0(X24)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(((r2_hidden(esk4_1(X24),u1_pre_topc(X24))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24))&(r2_hidden(esk5_1(X24),u1_pre_topc(X24))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~r2_hidden(k9_subset_1(u1_struct_0(X24),esk4_1(X24),esk5_1(X24)),u1_pre_topc(X24))|(~r2_hidden(k5_setfam_1(u1_struct_0(X24),esk3_1(X24)),u1_pre_topc(X24))|~r2_hidden(u1_struct_0(X24),u1_pre_topc(X24)))|v2_pre_topc(X24)|~l1_pre_topc(X24)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.39  fof(c_0_43, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.19/0.39  cnf(c_0_44, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  cnf(c_0_45, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.39  cnf(c_0_46, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  fof(c_0_47, negated_conjecture, (((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0)))!=u1_struct_0(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_43])])])])).
% 0.19/0.39  cnf(c_0_48, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_44, c_0_22])).
% 0.19/0.39  cnf(c_0_49, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk6_0)))!=u1_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.39  cnf(c_0_51, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_46])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 55
% 0.19/0.39  # Proof object clause steps            : 30
% 0.19/0.39  # Proof object formula steps           : 25
% 0.19/0.39  # Proof object conjectures             : 7
% 0.19/0.39  # Proof object clause conjectures      : 4
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 15
% 0.19/0.39  # Proof object initial formulas used   : 12
% 0.19/0.39  # Proof object generating inferences   : 13
% 0.19/0.39  # Proof object simplifying inferences  : 6
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 12
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 41
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 41
% 0.19/0.39  # Processed clauses                    : 244
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 55
% 0.19/0.39  # ...remaining for further processing  : 189
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 438
% 0.19/0.39  # ...of the previous two non-trivial   : 369
% 0.19/0.39  # Contextual simplify-reflections      : 4
% 0.19/0.39  # Paramodulations                      : 436
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 146
% 0.19/0.39  #    Positive orientable unit clauses  : 9
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 134
% 0.19/0.39  # Current number of unprocessed clauses: 204
% 0.19/0.39  # ...number of literals in the above   : 700
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 41
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1867
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 665
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 57
% 0.19/0.39  # Unit Clause-clause subsumption calls : 1
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 6
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 10816
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.044 s
% 0.19/0.39  # System time              : 0.007 s
% 0.19/0.39  # Total time               : 0.050 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

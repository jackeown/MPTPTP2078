%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:39 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 122 expanded)
%              Number of clauses        :   36 (  48 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  278 ( 775 expanded)
%              Number of equality atoms :   14 (  50 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r2_hidden(X4,X3)
                      <=> ( v3_pre_topc(X4,X1)
                          & v4_pre_topc(X4,X1)
                          & r2_hidden(X2,X4) ) ) )
                  & X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t5_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X4,X3)
                        <=> ( v3_pre_topc(X4,X1)
                            & v4_pre_topc(X4,X1)
                            & r2_hidden(X2,X4) ) ) )
                    & X3 = k1_xboole_0 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_connsp_2])).

fof(c_0_16,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_17,negated_conjecture,(
    ! [X36] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
      & ( v3_pre_topc(X36,esk4_0)
        | ~ r2_hidden(X36,esk6_0)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & ( v4_pre_topc(X36,esk4_0)
        | ~ r2_hidden(X36,esk6_0)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & ( r2_hidden(esk5_0,X36)
        | ~ r2_hidden(X36,esk6_0)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & ( ~ v3_pre_topc(X36,esk4_0)
        | ~ v4_pre_topc(X36,esk4_0)
        | ~ r2_hidden(esk5_0,X36)
        | r2_hidden(X36,esk6_0)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & esk6_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_18,plain,(
    ! [X29] :
      ( v2_struct_0(X29)
      | ~ l1_struct_0(X29)
      | ~ v1_xboole_0(u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X10] : m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_22,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_23,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | k3_subset_1(X8,X9) = k4_xboole_0(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_28,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_29,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_30,plain,(
    ! [X26,X27] :
      ( ( ~ v3_pre_topc(X27,X26)
        | r2_hidden(X27,u1_pre_topc(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ r2_hidden(X27,u1_pre_topc(X26))
        | v3_pre_topc(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_31,plain,(
    ! [X30] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | r2_hidden(k1_xboole_0,u1_pre_topc(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_39,plain,(
    ! [X31,X32] :
      ( ( ~ v3_pre_topc(X32,X31)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X31),X32),X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X31),X32),X31)
        | v3_pre_topc(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_40,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_49,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_51,plain,
    ( v3_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_20])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),k1_xboole_0)
    | ~ v4_pre_topc(u1_struct_0(esk4_0),esk4_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_54,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | ~ v3_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_41]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),k1_xboole_0)
    | ~ v3_pre_topc(u1_struct_0(esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_20])])).

cnf(c_0_57,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_47])).

fof(c_0_58,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r1_tarski(X20,u1_pre_topc(X19))
        | r2_hidden(k5_setfam_1(u1_struct_0(X19),X20),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(X21,u1_pre_topc(X19))
        | ~ r2_hidden(X22,u1_pre_topc(X19))
        | r2_hidden(k9_subset_1(u1_struct_0(X19),X21,X22),u1_pre_topc(X19))
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk2_1(X19),u1_pre_topc(X19))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))
        | m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk2_1(X19),u1_pre_topc(X19))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))
        | r1_tarski(esk1_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk2_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(esk3_1(X19),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))
        | ~ r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))
        | v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_59,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),k1_xboole_0)
    | ~ r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_20])])).

cnf(c_0_61,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_62,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_45]),c_0_20])])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:42:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.019 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.12/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.36  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.12/0.36  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.12/0.36  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.36  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.36  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.12/0.36  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.12/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.36  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.12/0.36  fof(t5_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>r2_hidden(k1_xboole_0,u1_pre_topc(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_pre_topc)).
% 0.12/0.36  fof(t30_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 0.12/0.36  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.12/0.36  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.36  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.12/0.36  fof(c_0_16, plain, ![X28]:(~l1_pre_topc(X28)|l1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.36  fof(c_0_17, negated_conjecture, ![X36]:(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(((((v3_pre_topc(X36,esk4_0)|~r2_hidden(X36,esk6_0)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk4_0))))&(v4_pre_topc(X36,esk4_0)|~r2_hidden(X36,esk6_0)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk4_0)))))&(r2_hidden(esk5_0,X36)|~r2_hidden(X36,esk6_0)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk4_0)))))&(~v3_pre_topc(X36,esk4_0)|~v4_pre_topc(X36,esk4_0)|~r2_hidden(esk5_0,X36)|r2_hidden(X36,esk6_0)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(esk4_0)))))&esk6_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.12/0.36  fof(c_0_18, plain, ![X29]:(v2_struct_0(X29)|~l1_struct_0(X29)|~v1_xboole_0(u1_struct_0(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.12/0.36  cnf(c_0_19, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  fof(c_0_21, plain, ![X10]:m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.12/0.36  fof(c_0_22, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.36  fof(c_0_23, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_25, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  fof(c_0_27, plain, ![X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|k3_subset_1(X8,X9)=k4_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.12/0.36  fof(c_0_28, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.12/0.36  fof(c_0_29, plain, ![X6]:k4_xboole_0(X6,k1_xboole_0)=X6, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.36  fof(c_0_30, plain, ![X26, X27]:((~v3_pre_topc(X27,X26)|r2_hidden(X27,u1_pre_topc(X26))|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(~r2_hidden(X27,u1_pre_topc(X26))|v3_pre_topc(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.12/0.36  fof(c_0_31, plain, ![X30]:(~v2_pre_topc(X30)|~l1_pre_topc(X30)|r2_hidden(k1_xboole_0,u1_pre_topc(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk6_0)|~v3_pre_topc(X1,esk4_0)|~v4_pre_topc(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_33, negated_conjecture, (esk6_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_34, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_35, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_36, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.12/0.36  fof(c_0_39, plain, ![X31, X32]:((~v3_pre_topc(X32,X31)|v4_pre_topc(k3_subset_1(u1_struct_0(X31),X32),X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))&(~v4_pre_topc(k3_subset_1(u1_struct_0(X31),X32),X31)|v3_pre_topc(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|~l1_pre_topc(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).
% 0.12/0.36  cnf(c_0_40, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_41, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.36  cnf(c_0_42, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  cnf(c_0_43, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.36  cnf(c_0_44, plain, (r2_hidden(k1_xboole_0,u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v4_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.36  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.12/0.36  cnf(c_0_49, plain, (v4_pre_topc(k3_subset_1(u1_struct_0(X2),X1),X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.36  cnf(c_0_50, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.12/0.36  cnf(c_0_51, plain, (v3_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)|~r2_hidden(k1_xboole_0,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_43, c_0_41])).
% 0.12/0.36  cnf(c_0_52, negated_conjecture, (r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_20])])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),k1_xboole_0)|~v4_pre_topc(u1_struct_0(esk4_0),esk4_0)|~v3_pre_topc(u1_struct_0(esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.12/0.36  cnf(c_0_54, plain, (v4_pre_topc(u1_struct_0(X1),X1)|~v3_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_41]), c_0_50])).
% 0.12/0.36  cnf(c_0_55, negated_conjecture, (v3_pre_topc(k1_xboole_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_20]), c_0_52])])).
% 0.12/0.36  cnf(c_0_56, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),k1_xboole_0)|~v3_pre_topc(u1_struct_0(esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_20])])).
% 0.12/0.36  cnf(c_0_57, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_43, c_0_47])).
% 0.12/0.36  fof(c_0_58, plain, ![X19, X20, X21, X22]:((((r2_hidden(u1_struct_0(X19),u1_pre_topc(X19))|~v2_pre_topc(X19)|~l1_pre_topc(X19))&(~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|(~r1_tarski(X20,u1_pre_topc(X19))|r2_hidden(k5_setfam_1(u1_struct_0(X19),X20),u1_pre_topc(X19)))|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(X21,u1_pre_topc(X19))|~r2_hidden(X22,u1_pre_topc(X19))|r2_hidden(k9_subset_1(u1_struct_0(X19),X21,X22),u1_pre_topc(X19))))|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(((m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk2_1(X19),u1_pre_topc(X19))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))|(m1_subset_1(esk1_1(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))&(((m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk2_1(X19),u1_pre_topc(X19))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))|(r1_tarski(esk1_1(X19),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))&((m1_subset_1(esk2_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&((m1_subset_1(esk3_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(((r2_hidden(esk2_1(X19),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19))&(r2_hidden(esk3_1(X19),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r2_hidden(k9_subset_1(u1_struct_0(X19),esk2_1(X19),esk3_1(X19)),u1_pre_topc(X19))|(~r2_hidden(k5_setfam_1(u1_struct_0(X19),esk1_1(X19)),u1_pre_topc(X19))|~r2_hidden(u1_struct_0(X19),u1_pre_topc(X19)))|v2_pre_topc(X19)|~l1_pre_topc(X19)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.12/0.36  fof(c_0_59, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.36  cnf(c_0_60, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),k1_xboole_0)|~r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_20])])).
% 0.12/0.36  cnf(c_0_61, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.36  fof(c_0_62, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.36  cnf(c_0_63, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.12/0.36  cnf(c_0_64, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_45]), c_0_20])])).
% 0.12/0.36  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.12/0.36  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 67
% 0.12/0.36  # Proof object clause steps            : 36
% 0.12/0.36  # Proof object formula steps           : 31
% 0.12/0.36  # Proof object conjectures             : 20
% 0.12/0.36  # Proof object clause conjectures      : 17
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 20
% 0.12/0.36  # Proof object initial formulas used   : 15
% 0.12/0.36  # Proof object generating inferences   : 14
% 0.12/0.36  # Proof object simplifying inferences  : 23
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 16
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 44
% 0.12/0.36  # Removed in clause preprocessing      : 1
% 0.12/0.36  # Initial clauses in saturation        : 43
% 0.12/0.36  # Processed clauses                    : 138
% 0.12/0.36  # ...of these trivial                  : 1
% 0.12/0.36  # ...subsumed                          : 5
% 0.12/0.36  # ...remaining for further processing  : 132
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 9
% 0.12/0.36  # Backward-rewritten                   : 7
% 0.12/0.36  # Generated clauses                    : 125
% 0.12/0.36  # ...of the previous two non-trivial   : 96
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 125
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 74
% 0.12/0.36  #    Positive orientable unit clauses  : 15
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 5
% 0.12/0.36  #    Non-unit-clauses                  : 54
% 0.12/0.36  # Current number of unprocessed clauses: 41
% 0.12/0.36  # ...number of literals in the above   : 214
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 59
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 1330
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 266
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 12
% 0.12/0.36  # Unit Clause-clause subsumption calls : 135
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 7
% 0.12/0.36  # BW rewrite match successes           : 3
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 6575
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.023 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.028 s
% 0.12/0.36  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

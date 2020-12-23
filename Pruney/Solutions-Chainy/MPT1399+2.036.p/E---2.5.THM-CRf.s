%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:39 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of clauses        :   36 (  49 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 ( 551 expanded)
%              Number of equality atoms :   23 (  53 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t50_subset_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ~ r2_hidden(X3,X2)
               => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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

fof(c_0_16,negated_conjecture,(
    ! [X31] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
      & ( v3_pre_topc(X31,esk2_0)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( v4_pre_topc(X31,esk2_0)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( r2_hidden(esk3_0,X31)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & ( ~ v3_pre_topc(X31,esk2_0)
        | ~ v4_pre_topc(X31,esk2_0)
        | ~ r2_hidden(esk3_0,X31)
        | r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk2_0))) )
      & esk4_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_17,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | ~ r1_tarski(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_18,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X12] : m1_subset_1(k2_subset_1(X12),k1_zfmisc_1(X12)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_24,plain,(
    ! [X11] : k2_subset_1(X11) = X11 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_25,plain,(
    ! [X13] : k2_subset_1(X13) = k3_subset_1(X13,k1_subset_1(X13)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_26,plain,(
    ! [X10] : k1_subset_1(X10) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X27] :
      ( ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v3_pre_topc(k2_struct_0(X27),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_32,plain,(
    ! [X23] :
      ( ~ l1_struct_0(X23)
      | k2_struct_0(X23) = u1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_33,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_34,plain,(
    ! [X15,X16,X17] :
      ( X15 = k1_xboole_0
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ m1_subset_1(X17,X15)
      | r2_hidden(X17,X16)
      | r2_hidden(X17,k3_subset_1(X15,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_subset_1])])])])).

fof(c_0_35,plain,(
    ! [X14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_36,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk2_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(sr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X26] :
      ( ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v4_pre_topc(k2_struct_0(X26),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,X2)
    | r2_hidden(X3,k3_subset_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_30]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk2_0),esk2_0)
    | ~ v4_pre_topc(u1_struct_0(esk2_0),esk2_0)
    | ~ r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( ~ v4_pre_topc(u1_struct_0(esk2_0),esk2_0)
    | ~ r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_55,plain,
    ( v4_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_41]),c_0_42])).

fof(c_0_56,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_57,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ v1_xboole_0(u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_49]),c_0_50])])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])]),c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_42]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n006.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 12:33:37 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.028 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.12/0.35  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.35  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.12/0.35  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.35  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.12/0.35  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.12/0.35  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.12/0.35  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.12/0.35  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.35  fof(t50_subset_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 0.12/0.35  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.12/0.35  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.12/0.35  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.35  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.12/0.35  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.12/0.35  fof(c_0_16, negated_conjecture, ![X31]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(((((v3_pre_topc(X31,esk2_0)|~r2_hidden(X31,esk4_0)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk2_0))))&(v4_pre_topc(X31,esk2_0)|~r2_hidden(X31,esk4_0)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk2_0)))))&(r2_hidden(esk3_0,X31)|~r2_hidden(X31,esk4_0)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk2_0)))))&(~v3_pre_topc(X31,esk2_0)|~v4_pre_topc(X31,esk2_0)|~r2_hidden(esk3_0,X31)|r2_hidden(X31,esk4_0)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk2_0)))))&esk4_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).
% 0.12/0.35  fof(c_0_17, plain, ![X21, X22]:(~r2_hidden(X21,X22)|~r1_tarski(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.35  fof(c_0_18, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.35  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,esk4_0)|~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~r2_hidden(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_20, negated_conjecture, (esk4_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.35  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.35  fof(c_0_23, plain, ![X12]:m1_subset_1(k2_subset_1(X12),k1_zfmisc_1(X12)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.12/0.35  fof(c_0_24, plain, ![X11]:k2_subset_1(X11)=X11, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.35  fof(c_0_25, plain, ![X13]:k2_subset_1(X13)=k3_subset_1(X13,k1_subset_1(X13)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.12/0.35  fof(c_0_26, plain, ![X10]:k1_subset_1(X10)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.12/0.35  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.35  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.35  cnf(c_0_29, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.35  cnf(c_0_30, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.35  fof(c_0_31, plain, ![X27]:(~v2_pre_topc(X27)|~l1_pre_topc(X27)|v3_pre_topc(k2_struct_0(X27),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.12/0.35  fof(c_0_32, plain, ![X23]:(~l1_struct_0(X23)|k2_struct_0(X23)=u1_struct_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.12/0.35  fof(c_0_33, plain, ![X24]:(~l1_pre_topc(X24)|l1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.35  fof(c_0_34, plain, ![X15, X16, X17]:(X15=k1_xboole_0|(~m1_subset_1(X16,k1_zfmisc_1(X15))|(~m1_subset_1(X17,X15)|(r2_hidden(X17,X16)|r2_hidden(X17,k3_subset_1(X15,X16)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_subset_1])])])])).
% 0.12/0.35  fof(c_0_35, plain, ![X14]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.12/0.35  cnf(c_0_36, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.35  cnf(c_0_37, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.35  cnf(c_0_38, negated_conjecture, (~v3_pre_topc(X1,esk2_0)|~v4_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,X1)), inference(sr,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.35  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.35  cnf(c_0_40, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.35  cnf(c_0_41, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.35  cnf(c_0_42, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.35  fof(c_0_43, plain, ![X26]:(~v2_pre_topc(X26)|~l1_pre_topc(X26)|v4_pre_topc(k2_struct_0(X26),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.12/0.35  cnf(c_0_44, plain, (X1=k1_xboole_0|r2_hidden(X3,X2)|r2_hidden(X3,k3_subset_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.35  cnf(c_0_45, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.35  cnf(c_0_46, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_30]), c_0_37])).
% 0.12/0.35  cnf(c_0_47, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk2_0),esk2_0)|~v4_pre_topc(u1_struct_0(esk2_0),esk2_0)|~r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.35  cnf(c_0_48, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.12/0.35  cnf(c_0_49, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_51, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.35  cnf(c_0_52, plain, (X1=k1_xboole_0|r2_hidden(X2,X1)|~m1_subset_1(X2,X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_28])).
% 0.12/0.35  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_54, negated_conjecture, (~v4_pre_topc(u1_struct_0(esk2_0),esk2_0)|~r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])])).
% 0.12/0.35  cnf(c_0_55, plain, (v4_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_41]), c_0_42])).
% 0.12/0.35  fof(c_0_56, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.35  fof(c_0_57, plain, ![X25]:(v2_struct_0(X25)|~l1_struct_0(X25)|~v1_xboole_0(u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.12/0.35  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.35  cnf(c_0_59, negated_conjecture, (~r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_49]), c_0_50])])).
% 0.12/0.35  cnf(c_0_60, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.35  cnf(c_0_61, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.35  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.35  cnf(c_0_63, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_60])).
% 0.12/0.35  cnf(c_0_64, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_65, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])]), c_0_64])).
% 0.12/0.35  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_42]), c_0_50])]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 67
% 0.12/0.35  # Proof object clause steps            : 36
% 0.12/0.35  # Proof object formula steps           : 31
% 0.12/0.35  # Proof object conjectures             : 18
% 0.12/0.35  # Proof object clause conjectures      : 15
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 20
% 0.12/0.35  # Proof object initial formulas used   : 15
% 0.12/0.35  # Proof object generating inferences   : 11
% 0.12/0.35  # Proof object simplifying inferences  : 21
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 16
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 26
% 0.12/0.35  # Removed in clause preprocessing      : 2
% 0.12/0.35  # Initial clauses in saturation        : 24
% 0.12/0.35  # Processed clauses                    : 74
% 0.12/0.35  # ...of these trivial                  : 1
% 0.12/0.35  # ...subsumed                          : 9
% 0.12/0.35  # ...remaining for further processing  : 64
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 1
% 0.12/0.35  # Backward-rewritten                   : 6
% 0.12/0.35  # Generated clauses                    : 32
% 0.12/0.35  # ...of the previous two non-trivial   : 32
% 0.12/0.35  # Contextual simplify-reflections      : 2
% 0.12/0.35  # Paramodulations                      : 31
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 0
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 33
% 0.12/0.35  #    Positive orientable unit clauses  : 12
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 3
% 0.12/0.35  #    Non-unit-clauses                  : 18
% 0.12/0.35  # Current number of unprocessed clauses: 5
% 0.12/0.35  # ...number of literals in the above   : 20
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 33
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 120
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 62
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.35  # Unit Clause-clause subsumption calls : 26
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 2
% 0.12/0.35  # BW rewrite match successes           : 1
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 2215
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.031 s
% 0.12/0.35  # System time              : 0.003 s
% 0.12/0.35  # Total time               : 0.034 s
% 0.12/0.35  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:10:42 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 364 expanded)
%              Number of clauses        :   62 ( 177 expanded)
%              Number of leaves         :   18 (  93 expanded)
%              Depth                    :   21
%              Number of atoms          :  229 (1095 expanded)
%              Number of equality atoms :   74 ( 397 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t43_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(cc2_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

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

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_17,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ( k4_xboole_0(X15,X16) != k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | k4_xboole_0(X15,X16) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

fof(c_0_24,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,plain,
    ( X1 != k1_xboole_0
    | ~ r1_tarski(X2,X3)
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_28,plain,
    ( X1 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_33,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | X2 != k1_xboole_0
    | ~ r2_hidden(esk1_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_35,plain,
    ( X1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_36,plain,
    ( X1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))
    | X1 != k1_xboole_0
    | ~ r2_hidden(esk1_3(k1_xboole_0,X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( X1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_43,plain,
    ( ~ epred1_0
  <=> ! [X2,X3] : ~ r1_tarski(X2,X3) ),
    introduced(definition)).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_20])).

fof(c_0_45,plain,
    ( ~ epred2_0
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( epred1_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_equiv,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_50,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_23]),c_0_47]),c_0_43]),c_0_45])).

cnf(c_0_51,plain,
    ( epred1_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,plain,
    ( ~ epred2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_54,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_20])).

fof(c_0_55,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k1_tops_1(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t43_tops_1])).

fof(c_0_56,plain,(
    ! [X23] : k2_subset_1(X23) = k3_subset_1(X23,k1_subset_1(X23)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_57,plain,(
    ! [X20] : k2_subset_1(X20) = X20 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_58,plain,(
    ! [X19] : k1_subset_1(X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_45]),c_0_53])).

cnf(c_0_60,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X2))
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_32])).

fof(c_0_61,plain,(
    ! [X35,X36] :
      ( ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | ~ v1_xboole_0(X36)
      | v4_pre_topc(X36,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).

fof(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & k1_tops_1(esk3_0,k2_struct_0(esk3_0)) != k2_struct_0(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).

fof(c_0_63,plain,(
    ! [X37] :
      ( ~ l1_struct_0(X37)
      | k2_struct_0(X37) = u1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_64,plain,(
    ! [X38] :
      ( ~ l1_pre_topc(X38)
      | l1_struct_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_65,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k3_subset_1(X21,k3_subset_1(X21,X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_66,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_70,plain,(
    ! [X39,X40] :
      ( ( ~ v4_pre_topc(X40,X39)
        | k2_pre_topc(X39,X40) = X40
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) )
      & ( ~ v2_pre_topc(X39)
        | k2_pre_topc(X39,X40) != X40
        | v4_pre_topc(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_71,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_73,negated_conjecture,
    ( k1_tops_1(esk3_0,k2_struct_0(esk3_0)) != k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_77,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | k1_tops_1(X41,X42) = k3_subset_1(u1_struct_0(X41),k2_pre_topc(X41,k3_subset_1(u1_struct_0(X41),X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_78,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_69])).

cnf(c_0_82,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_83,plain,
    ( v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_29]),c_0_72])])).

cnf(c_0_84,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_85,negated_conjecture,
    ( k1_tops_1(esk3_0,u1_struct_0(esk3_0)) != u1_struct_0(esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_87,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_88,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_29])])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,plain,
    ( k2_pre_topc(X1,k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_29])).

cnf(c_0_91,negated_conjecture,
    ( v4_pre_topc(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_76])])).

cnf(c_0_92,negated_conjecture,
    ( k1_tops_1(esk3_0,u1_struct_0(esk3_0)) != u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_93,plain,
    ( k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_94,negated_conjecture,
    ( k2_pre_topc(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_76]),c_0_91])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_79]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.38  fof(t43_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 0.13/0.38  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.13/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.38  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.13/0.38  fof(cc2_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 0.13/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.13/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.13/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.38  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 0.13/0.38  fof(c_0_16, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  fof(c_0_18, plain, ![X15, X16]:((k4_xboole_0(X15,X16)!=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|k4_xboole_0(X15,X16)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.38  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_22, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_23, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.13/0.38  fof(c_0_24, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_25, plain, (X1!=k1_xboole_0|~r1_tarski(X2,X3)|~r2_hidden(X4,X1)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  fof(c_0_27, plain, ![X24]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.38  cnf(c_0_28, plain, (X1!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r2_hidden(X4,X1)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_29, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_30, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_31, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_32, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_30, c_0_20])).
% 0.13/0.38  cnf(c_0_33, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X1)|X2!=k1_xboole_0|~r2_hidden(esk1_3(X2,X3,X1),X4)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_34, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),X1)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 0.13/0.38  cnf(c_0_35, plain, (X1=k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(er,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_36, plain, (X1=k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))|X1!=k1_xboole_0|~r2_hidden(esk1_3(k1_xboole_0,X2,X1),X3)), inference(spm,[status(thm)],[c_0_31, c_0_35])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_38, plain, (X1=k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_37, c_0_20])).
% 0.13/0.38  cnf(c_0_41, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_42, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(er,[status(thm)],[c_0_38])).
% 0.13/0.38  fof(c_0_43, plain, (~epred1_0<=>![X2, X3]:~r1_tarski(X2,X3)), introduced(definition)).
% 0.13/0.38  cnf(c_0_44, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_20])).
% 0.13/0.38  fof(c_0_45, plain, (~epred2_0<=>![X1]:~r2_hidden(X1,k1_xboole_0)), introduced(definition)).
% 0.13/0.38  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_48, plain, (epred1_0|~r1_tarski(X1,X2)), inference(split_equiv,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_49, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.13/0.38  cnf(c_0_50, plain, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_23]), c_0_47]), c_0_43]), c_0_45])).
% 0.13/0.38  cnf(c_0_51, plain, (epred1_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_52, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_53, plain, (~epred2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.13/0.38  cnf(c_0_54, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_52, c_0_20])).
% 0.13/0.38  fof(c_0_55, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>k1_tops_1(X1,k2_struct_0(X1))=k2_struct_0(X1))), inference(assume_negation,[status(cth)],[t43_tops_1])).
% 0.13/0.38  fof(c_0_56, plain, ![X23]:k2_subset_1(X23)=k3_subset_1(X23,k1_subset_1(X23)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.13/0.38  fof(c_0_57, plain, ![X20]:k2_subset_1(X20)=X20, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.38  fof(c_0_58, plain, ![X19]:k1_subset_1(X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.13/0.38  cnf(c_0_59, plain, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_45]), c_0_53])).
% 0.13/0.38  cnf(c_0_60, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X2))|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_54, c_0_32])).
% 0.13/0.38  fof(c_0_61, plain, ![X35, X36]:(~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(~v1_xboole_0(X36)|v4_pre_topc(X36,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).
% 0.13/0.38  fof(c_0_62, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&k1_tops_1(esk3_0,k2_struct_0(esk3_0))!=k2_struct_0(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_55])])])).
% 0.13/0.38  fof(c_0_63, plain, ![X37]:(~l1_struct_0(X37)|k2_struct_0(X37)=u1_struct_0(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.38  fof(c_0_64, plain, ![X38]:(~l1_pre_topc(X38)|l1_struct_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  fof(c_0_65, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|k3_subset_1(X21,k3_subset_1(X21,X22))=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.13/0.38  cnf(c_0_66, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_67, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.38  cnf(c_0_68, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.38  cnf(c_0_69, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  fof(c_0_70, plain, ![X39, X40]:((~v4_pre_topc(X40,X39)|k2_pre_topc(X39,X40)=X40|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))&(~v2_pre_topc(X39)|k2_pre_topc(X39,X40)!=X40|v4_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|~l1_pre_topc(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.13/0.38  cnf(c_0_71, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.38  cnf(c_0_72, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (k1_tops_1(esk3_0,k2_struct_0(esk3_0))!=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.38  cnf(c_0_74, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.38  cnf(c_0_75, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.38  fof(c_0_77, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|k1_tops_1(X41,X42)=k3_subset_1(u1_struct_0(X41),k2_pre_topc(X41,k3_subset_1(u1_struct_0(X41),X42))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.13/0.38  cnf(c_0_78, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.38  cnf(c_0_79, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.13/0.38  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_81, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_44, c_0_69])).
% 0.13/0.38  cnf(c_0_82, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.38  cnf(c_0_83, plain, (v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_29]), c_0_72])])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (k1_tops_1(esk3_0,u1_struct_0(esk3_0))!=u1_struct_0(esk3_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.13/0.38  cnf(c_0_87, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.13/0.38  cnf(c_0_88, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_29])])).
% 0.13/0.38  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.13/0.38  cnf(c_0_90, plain, (k2_pre_topc(X1,k1_xboole_0)=k1_xboole_0|~v4_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_82, c_0_29])).
% 0.13/0.38  cnf(c_0_91, negated_conjecture, (v4_pre_topc(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_76])])).
% 0.13/0.38  cnf(c_0_92, negated_conjecture, (k1_tops_1(esk3_0,u1_struct_0(esk3_0))!=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.13/0.38  cnf(c_0_93, plain, (k1_tops_1(X1,u1_struct_0(X1))=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])])).
% 0.13/0.38  cnf(c_0_94, negated_conjecture, (k2_pre_topc(esk3_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_76]), c_0_91])])).
% 0.13/0.38  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_79]), c_0_76])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 96
% 0.13/0.38  # Proof object clause steps            : 62
% 0.13/0.38  # Proof object formula steps           : 34
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 24
% 0.13/0.38  # Proof object initial formulas used   : 16
% 0.13/0.38  # Proof object generating inferences   : 28
% 0.13/0.38  # Proof object simplifying inferences  : 30
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 18
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 30
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 27
% 0.13/0.38  # Processed clauses                    : 153
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 25
% 0.13/0.38  # ...remaining for further processing  : 126
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 6
% 0.13/0.38  # Backward-rewritten                   : 9
% 0.13/0.38  # Generated clauses                    : 290
% 0.13/0.38  # ...of the previous two non-trivial   : 247
% 0.13/0.38  # Contextual simplify-reflections      : 3
% 0.13/0.38  # Paramodulations                      : 271
% 0.13/0.38  # Factorizations                       : 2
% 0.13/0.38  # Equation resolutions                 : 11
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 82
% 0.13/0.38  #    Positive orientable unit clauses  : 16
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 61
% 0.13/0.38  # Current number of unprocessed clauses: 139
% 0.13/0.38  # ...number of literals in the above   : 495
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 45
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 690
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 410
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 28
% 0.13/0.38  # Unit Clause-clause subsumption calls : 177
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 26
% 0.13/0.38  # BW rewrite match successes           : 5
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6072
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.042 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

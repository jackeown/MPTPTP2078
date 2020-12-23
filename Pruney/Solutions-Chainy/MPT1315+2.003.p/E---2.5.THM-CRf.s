%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:19 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 208 expanded)
%              Number of clauses        :   43 (  86 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  203 ( 893 expanded)
%              Number of equality atoms :   46 ( 181 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t34_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v4_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(t43_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v4_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v4_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k9_subset_1(X22,X23,X24) = k3_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( v4_pre_topc(X2,X1)
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                     => ( X4 = X2
                       => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_tops_2])).

cnf(c_0_17,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_pre_topc(esk5_0,esk3_0)
    & v4_pre_topc(esk4_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & esk6_0 = esk4_0
    & ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X31,X32,X33,X35] :
      ( ( m1_subset_1(esk2_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v4_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_pre_topc(X32,X31)
        | ~ l1_pre_topc(X31) )
      & ( v4_pre_topc(esk2_3(X31,X32,X33),X31)
        | ~ v4_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_pre_topc(X32,X31)
        | ~ l1_pre_topc(X31) )
      & ( k9_subset_1(u1_struct_0(X32),esk2_3(X31,X32,X33),k2_struct_0(X32)) = X33
        | ~ v4_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_pre_topc(X32,X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v4_pre_topc(X35,X31)
        | k9_subset_1(u1_struct_0(X32),X35,k2_struct_0(X32)) != X33
        | v4_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_pre_topc(X32,X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).

fof(c_0_25,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k9_subset_1(X16,X17,X18) = k9_subset_1(X16,X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_26,plain,
    ( k9_subset_1(X1,X2,X3) = X3
    | r2_hidden(esk1_3(X2,X3,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( v4_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),X1,esk4_0) = esk4_0
    | r2_hidden(esk1_3(X1,esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_33,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ r2_hidden(X21,X20)
      | r2_hidden(X21,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_34,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk4_0,X1) = esk4_0
    | r2_hidden(esk1_3(X1,esk4_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_27])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v4_pre_topc(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_23])).

fof(c_0_37,plain,(
    ! [X27] :
      ( ~ l1_struct_0(X27)
      | k2_struct_0(X27) = u1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_38,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_39,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | l1_pre_topc(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_40,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_tarski(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_41,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_15])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_3(k2_struct_0(esk5_0),esk4_0,esk4_0),esk4_0)
    | ~ v4_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_27])]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(k2_struct_0(esk5_0),esk4_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_55,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_46]),c_0_47])])).

cnf(c_0_57,plain,
    ( k9_subset_1(X1,X2,X3) = k1_setfam_1(k2_tarski(X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k1_setfam_1(k2_tarski(u1_struct_0(esk5_0),X1)) = X1
    | ~ r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk5_0),esk4_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_60,plain,
    ( k9_subset_1(X1,X2,X3) = k1_setfam_1(k2_tarski(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk5_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_51])).

cnf(c_0_62,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_55]),c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(X1,esk4_0,u1_struct_0(esk5_0)) = esk4_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( ~ v4_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_27])]),c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_44]),c_0_45]),c_0_46]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:26:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.029 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.46  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.46  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.20/0.46  fof(t34_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 0.20/0.46  fof(t43_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X3,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v4_pre_topc(X4,X1))&k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_pre_topc)).
% 0.20/0.46  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.20/0.46  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.46  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.46  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.46  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.46  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.46  fof(c_0_11, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.46  fof(c_0_12, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.46  fof(c_0_13, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X22))|k9_subset_1(X22,X23,X24)=k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.20/0.46  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.46  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3)))))))), inference(assume_negation,[status(cth)],[t34_tops_2])).
% 0.20/0.46  cnf(c_0_17, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.46  cnf(c_0_18, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.46  fof(c_0_19, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_pre_topc(esk5_0,esk3_0)&(v4_pre_topc(esk4_0,esk3_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(esk6_0=esk4_0&~v4_pre_topc(esk6_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.46  cnf(c_0_20, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_17, c_0_15])).
% 0.20/0.46  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_18])).
% 0.20/0.46  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_23, negated_conjecture, (esk6_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  fof(c_0_24, plain, ![X31, X32, X33, X35]:((((m1_subset_1(esk2_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))|~v4_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~m1_pre_topc(X32,X31)|~l1_pre_topc(X31))&(v4_pre_topc(esk2_3(X31,X32,X33),X31)|~v4_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~m1_pre_topc(X32,X31)|~l1_pre_topc(X31)))&(k9_subset_1(u1_struct_0(X32),esk2_3(X31,X32,X33),k2_struct_0(X32))=X33|~v4_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~m1_pre_topc(X32,X31)|~l1_pre_topc(X31)))&(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X31)))|~v4_pre_topc(X35,X31)|k9_subset_1(u1_struct_0(X32),X35,k2_struct_0(X32))!=X33|v4_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~m1_pre_topc(X32,X31)|~l1_pre_topc(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).
% 0.20/0.46  fof(c_0_25, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X16))|k9_subset_1(X16,X17,X18)=k9_subset_1(X16,X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.20/0.46  cnf(c_0_26, plain, (k9_subset_1(X1,X2,X3)=X3|r2_hidden(esk1_3(X2,X3,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.46  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.46  cnf(c_0_28, plain, (v4_pre_topc(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3))!=X4|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.46  cnf(c_0_29, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.46  cnf(c_0_30, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),X1,esk4_0)=esk4_0|r2_hidden(esk1_3(X1,esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.46  cnf(c_0_31, negated_conjecture, (~v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_32, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.46  fof(c_0_33, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|(~r2_hidden(X21,X20)|r2_hidden(X21,X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.46  cnf(c_0_34, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.46  cnf(c_0_35, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk4_0,X1)=esk4_0|r2_hidden(esk1_3(X1,esk4_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_27])])).
% 0.20/0.46  cnf(c_0_36, negated_conjecture, (~v4_pre_topc(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_31, c_0_23])).
% 0.20/0.46  fof(c_0_37, plain, ![X27]:(~l1_struct_0(X27)|k2_struct_0(X27)=u1_struct_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.46  fof(c_0_38, plain, ![X28]:(~l1_pre_topc(X28)|l1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.46  fof(c_0_39, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|l1_pre_topc(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.46  fof(c_0_40, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_tarski(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.46  cnf(c_0_41, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_32, c_0_15])).
% 0.20/0.46  cnf(c_0_42, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.46  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_3(k2_struct_0(esk5_0),esk4_0,esk4_0),esk4_0)|~v4_pre_topc(esk4_0,X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_27])]), c_0_36])).
% 0.20/0.46  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_45, negated_conjecture, (v4_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_48, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.46  cnf(c_0_49, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.46  cnf(c_0_50, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.46  cnf(c_0_51, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.46  cnf(c_0_52, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_21]), c_0_21])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 0.20/0.46  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(k2_struct_0(esk5_0),esk4_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.46  cnf(c_0_55, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.46  cnf(c_0_56, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_46]), c_0_47])])).
% 0.20/0.46  cnf(c_0_57, plain, (k9_subset_1(X1,X2,X3)=k1_setfam_1(k2_tarski(X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_51])).
% 0.20/0.46  cnf(c_0_58, negated_conjecture, (k1_setfam_1(k2_tarski(u1_struct_0(esk5_0),X1))=X1|~r2_hidden(esk1_3(u1_struct_0(esk5_0),X1,X1),esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.46  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk5_0),esk4_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.20/0.46  cnf(c_0_60, plain, (k9_subset_1(X1,X2,X3)=k1_setfam_1(k2_tarski(X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_57])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,u1_struct_0(esk5_0)))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_51])).
% 0.20/0.46  cnf(c_0_62, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_55]), c_0_50])).
% 0.20/0.46  cnf(c_0_63, negated_conjecture, (k9_subset_1(X1,esk4_0,u1_struct_0(esk5_0))=esk4_0|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (~v4_pre_topc(esk4_0,X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_27])]), c_0_36])).
% 0.20/0.46  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_44]), c_0_45]), c_0_46]), c_0_47])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 66
% 0.20/0.46  # Proof object clause steps            : 43
% 0.20/0.46  # Proof object formula steps           : 23
% 0.20/0.46  # Proof object conjectures             : 24
% 0.20/0.46  # Proof object clause conjectures      : 21
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 18
% 0.20/0.46  # Proof object initial formulas used   : 11
% 0.20/0.46  # Proof object generating inferences   : 19
% 0.20/0.46  # Proof object simplifying inferences  : 29
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 11
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 25
% 0.20/0.46  # Removed in clause preprocessing      : 1
% 0.20/0.46  # Initial clauses in saturation        : 24
% 0.20/0.46  # Processed clauses                    : 481
% 0.20/0.46  # ...of these trivial                  : 5
% 0.20/0.46  # ...subsumed                          : 258
% 0.20/0.46  # ...remaining for further processing  : 218
% 0.20/0.46  # Other redundant clauses eliminated   : 4
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 3
% 0.20/0.46  # Backward-rewritten                   : 1
% 0.20/0.46  # Generated clauses                    : 2842
% 0.20/0.46  # ...of the previous two non-trivial   : 2624
% 0.20/0.46  # Contextual simplify-reflections      : 9
% 0.20/0.46  # Paramodulations                      : 2812
% 0.20/0.46  # Factorizations                       : 26
% 0.20/0.46  # Equation resolutions                 : 4
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 186
% 0.20/0.46  #    Positive orientable unit clauses  : 11
% 0.20/0.46  #    Positive unorientable unit clauses: 1
% 0.20/0.46  #    Negative unit clauses             : 1
% 0.20/0.46  #    Non-unit-clauses                  : 173
% 0.20/0.46  # Current number of unprocessed clauses: 2176
% 0.20/0.46  # ...number of literals in the above   : 12497
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 29
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 8209
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 4256
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 270
% 0.20/0.46  # Unit Clause-clause subsumption calls : 35
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 6
% 0.20/0.46  # BW rewrite match successes           : 1
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 63295
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.105 s
% 0.20/0.46  # System time              : 0.006 s
% 0.20/0.46  # Total time               : 0.112 s
% 0.20/0.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

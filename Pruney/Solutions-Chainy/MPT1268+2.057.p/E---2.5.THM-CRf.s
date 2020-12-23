%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 209 expanded)
%              Number of clauses        :   36 (  78 expanded)
%              Number of leaves         :   10 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 (1341 expanded)
%              Number of equality atoms :   26 ( 169 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X1) )
                 => X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t54_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,k1_tops_1(X1,X3))
          <=> ? [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                & v3_pre_topc(X4,X1)
                & r1_tarski(X4,X3)
                & r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X1) )
                   => X3 = k1_xboole_0 ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_tops_1])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,negated_conjecture,(
    ! [X33] :
      ( v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( r1_tarski(esk5_0,esk4_0)
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( v3_pre_topc(esk5_0,esk3_0)
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( esk5_0 != k1_xboole_0
        | ~ v2_tops_1(esk4_0,esk3_0) )
      & ( v2_tops_1(esk4_0,esk3_0)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r1_tarski(X33,esk4_0)
        | ~ v3_pre_topc(X33,esk3_0)
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X27] :
      ( ( m1_subset_1(esk2_3(X23,X24,X25),k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X24,k1_tops_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( v3_pre_topc(esk2_3(X23,X24,X25),X23)
        | ~ r2_hidden(X24,k1_tops_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r1_tarski(esk2_3(X23,X24,X25),X25)
        | ~ r2_hidden(X24,k1_tops_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(X24,esk2_3(X23,X24,X25))
        | ~ r2_hidden(X24,k1_tops_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v3_pre_topc(X27,X23)
        | ~ r1_tarski(X27,X25)
        | ~ r2_hidden(X24,X27)
        | r2_hidden(X24,k1_tops_1(X23,X25))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).

cnf(c_0_17,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0)
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_21,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | ~ r1_tarski(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_22,plain,
    ( r2_hidden(X4,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0)
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_29,plain,(
    ! [X19,X20] :
      ( ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | v3_pre_topc(k1_tops_1(X19,X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | r1_tarski(k1_tops_1(X21,X22),X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_31,plain,(
    ! [X28,X29] :
      ( ( ~ v2_tops_1(X29,X28)
        | k1_tops_1(X28,X29) = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( k1_tops_1(X28,X29) != k1_xboole_0
        | v2_tops_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk3_0,X2))
    | ~ v2_tops_1(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_tops_1(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X2),X1)
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0)
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_40,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_41,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k1_tops_1(esk3_0,X1) = k1_xboole_0
    | v2_tops_1(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk3_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24]),c_0_25])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_15]),c_0_24])])).

cnf(c_0_44,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_xboole_0
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_15]),c_0_24])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_tops_1(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r1_tarski(k1_tops_1(esk3_0,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_15]),c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0)
    | k1_tops_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_15]),c_0_24])])).

cnf(c_0_48,negated_conjecture,
    ( k1_tops_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_15]),c_0_43])]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_tops_1(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_44]),c_0_46])])).

cnf(c_0_50,negated_conjecture,
    ( v2_tops_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

fof(c_0_51,plain,(
    ! [X14,X16,X17,X18] :
      ( ( r2_hidden(esk1_1(X14),X14)
        | X14 = k1_xboole_0 )
      & ( ~ r2_hidden(X16,X14)
        | esk1_1(X14) != k3_mcart_1(X16,X17,X18)
        | X14 = k1_xboole_0 )
      & ( ~ r2_hidden(X17,X14)
        | esk1_1(X14) != k3_mcart_1(X16,X17,X18)
        | X14 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v2_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_50])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.046 s
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t86_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.41  fof(t54_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k1_tops_1(X1,X3))<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 0.20/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.41  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.20/0.41  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.20/0.41  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 0.20/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.41  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.20/0.41  fof(c_0_10, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v3_pre_topc(X3,X1))=>X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t86_tops_1])).
% 0.20/0.41  fof(c_0_11, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  fof(c_0_12, negated_conjecture, ![X33]:((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v2_tops_1(esk4_0,esk3_0))&(((r1_tarski(esk5_0,esk4_0)|~v2_tops_1(esk4_0,esk3_0))&(v3_pre_topc(esk5_0,esk3_0)|~v2_tops_1(esk4_0,esk3_0)))&(esk5_0!=k1_xboole_0|~v2_tops_1(esk4_0,esk3_0))))&(v2_tops_1(esk4_0,esk3_0)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~r1_tarski(X33,esk4_0)|~v3_pre_topc(X33,esk3_0)|X33=k1_xboole_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 0.20/0.41  fof(c_0_13, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.41  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  fof(c_0_16, plain, ![X23, X24, X25, X27]:(((((m1_subset_1(esk2_3(X23,X24,X25),k1_zfmisc_1(u1_struct_0(X23)))|~r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(v3_pre_topc(esk2_3(X23,X24,X25),X23)|~r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~v2_pre_topc(X23)|~l1_pre_topc(X23))))&(r1_tarski(esk2_3(X23,X24,X25),X25)|~r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~v2_pre_topc(X23)|~l1_pre_topc(X23))))&(r2_hidden(X24,esk2_3(X23,X24,X25))|~r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~v2_pre_topc(X23)|~l1_pre_topc(X23))))&(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X23)))|~v3_pre_topc(X27,X23)|~r1_tarski(X27,X25)|~r2_hidden(X24,X27)|r2_hidden(X24,k1_tops_1(X23,X25))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~v2_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_tops_1])])])])])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)|X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)|~v3_pre_topc(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.41  fof(c_0_21, plain, ![X12, X13]:(~r2_hidden(X12,X13)|~r1_tarski(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.41  cnf(c_0_22, plain, (r2_hidden(X4,k1_tops_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (X1=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.41  fof(c_0_29, plain, ![X19, X20]:(~v2_pre_topc(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v3_pre_topc(k1_tops_1(X19,X20),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.20/0.41  fof(c_0_30, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|r1_tarski(k1_tops_1(X21,X22),X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.20/0.41  fof(c_0_31, plain, ![X28, X29]:((~v2_tops_1(X29,X28)|k1_tops_1(X28,X29)=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(k1_tops_1(X28,X29)!=k1_xboole_0|v2_tops_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.20/0.41  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk3_0,X2))|~v2_tops_1(esk4_0,esk3_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk5_0,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (X1=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~v3_pre_topc(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_35, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_37, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (~v2_tops_1(esk4_0,esk3_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X2),X1)|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (r1_tarski(esk5_0,esk4_0)|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  fof(c_0_40, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.41  cnf(c_0_41, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (k1_tops_1(esk3_0,X1)=k1_xboole_0|v2_tops_1(esk4_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tops_1(esk3_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_24]), c_0_25])])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_tops_1(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_15]), c_0_24])])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_xboole_0|~v2_tops_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_15]), c_0_24])])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (~v2_tops_1(esk4_0,esk3_0)|~r2_hidden(X1,esk5_0)|~r1_tarski(k1_tops_1(esk3_0,esk4_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_15]), c_0_39])).
% 0.20/0.41  cnf(c_0_46, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)|k1_tops_1(esk3_0,esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_15]), c_0_24])])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k1_tops_1(esk3_0,esk4_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_15]), c_0_43])]), c_0_44])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (~v2_tops_1(esk4_0,esk3_0)|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_44]), c_0_46])])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (v2_tops_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])])).
% 0.20/0.41  fof(c_0_51, plain, ![X14, X16, X17, X18]:((r2_hidden(esk1_1(X14),X14)|X14=k1_xboole_0)&((~r2_hidden(X16,X14)|esk1_1(X14)!=k3_mcart_1(X16,X17,X18)|X14=k1_xboole_0)&(~r2_hidden(X17,X14)|esk1_1(X14)!=k3_mcart_1(X16,X17,X18)|X14=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (esk5_0!=k1_xboole_0|~v2_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.20/0.41  cnf(c_0_54, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_50])])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 57
% 0.20/0.41  # Proof object clause steps            : 36
% 0.20/0.41  # Proof object formula steps           : 21
% 0.20/0.41  # Proof object conjectures             : 28
% 0.20/0.41  # Proof object clause conjectures      : 25
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 19
% 0.20/0.41  # Proof object initial formulas used   : 10
% 0.20/0.41  # Proof object generating inferences   : 14
% 0.20/0.41  # Proof object simplifying inferences  : 26
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 10
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 25
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 25
% 0.20/0.41  # Processed clauses                    : 186
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 67
% 0.20/0.41  # ...remaining for further processing  : 119
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 22
% 0.20/0.41  # Backward-rewritten                   : 31
% 0.20/0.41  # Generated clauses                    : 295
% 0.20/0.41  # ...of the previous two non-trivial   : 266
% 0.20/0.41  # Contextual simplify-reflections      : 11
% 0.20/0.41  # Paramodulations                      : 295
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 66
% 0.20/0.41  #    Positive orientable unit clauses  : 10
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 4
% 0.20/0.41  #    Non-unit-clauses                  : 52
% 0.20/0.41  # Current number of unprocessed clauses: 94
% 0.20/0.41  # ...number of literals in the above   : 461
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 53
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 2455
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 844
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 97
% 0.20/0.41  # Unit Clause-clause subsumption calls : 147
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 3
% 0.20/0.41  # BW rewrite match successes           : 3
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 8044
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.068 s
% 0.20/0.41  # System time              : 0.004 s
% 0.20/0.41  # Total time               : 0.072 s
% 0.20/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

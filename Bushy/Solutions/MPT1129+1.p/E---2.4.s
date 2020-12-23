%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : pre_topc__t60_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:45 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   76 (1074 expanded)
%              Number of clauses        :   53 ( 463 expanded)
%              Number of leaves         :   11 ( 272 expanded)
%              Depth                    :   14
%              Number of atoms          :  224 (4127 expanded)
%              Number of equality atoms :   16 ( 240 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v3_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',t60_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',dt_u1_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',d5_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',abstractness_v1_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',dt_g1_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',t1_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',t2_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t60_pre_topc.p',t3_subset)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v3_pre_topc(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_pre_topc])).

fof(c_0_12,plain,(
    ! [X20,X21,X22,X23] :
      ( ( X20 = X22
        | g1_pre_topc(X20,X21) != g1_pre_topc(X22,X23)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))) )
      & ( X21 = X23
        | g1_pre_topc(X20,X21) != g1_pre_topc(X22,X23)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_13,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | m1_subset_1(u1_pre_topc(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ( ~ v3_pre_topc(X11,X10)
        | r2_hidden(X11,u1_pre_topc(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(X11,u1_pre_topc(X10))
        | v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ( ~ v3_pre_topc(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      | ~ v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) )
    & ( v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | v3_pre_topc(esk2_0,esk1_0) )
    & ( v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | ~ v1_pre_topc(X7)
      | X7 = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ( v1_pre_topc(g1_pre_topc(X12,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) )
      & ( l1_pre_topc(g1_pre_topc(X12,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_20,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | m1_subset_1(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_21,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | m1_subset_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X37,X38] :
      ( ~ r2_hidden(X37,X38)
      | ~ v1_xboole_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_33,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_34,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_35,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17])).

fof(c_0_39,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_44,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_pre_topc(esk1_0))
    | v3_pre_topc(esk2_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_47,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ v1_xboole_0(u1_pre_topc(esk1_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_42])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( v1_xboole_0(u1_pre_topc(X1))
    | v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_pre_topc(esk1_0))
    | v3_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_42])])).

cnf(c_0_51,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0)
    | ~ v1_xboole_0(u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_35]),c_0_42])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk2_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v3_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v3_pre_topc(esk2_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_42])]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk2_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_52]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk2_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])]),c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_42])])).

fof(c_0_60,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,u1_pre_topc(esk1_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_42])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_35]),c_0_42])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | m1_subset_1(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_35]),c_0_42])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(u1_pre_topc(esk1_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_41]),c_0_42])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_38]),c_0_42])])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ r1_tarski(X1,u1_struct_0(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0))
    | m1_subset_1(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_xboole_0(u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_35]),c_0_42])])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk1_0))
    | ~ m1_subset_1(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_45])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_55]),c_0_42])]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_71]),c_0_55]),c_0_42])]),c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t25_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:37 EDT 2019

% Result     : Theorem 151.46s
% Output     : CNFRefutation 151.46s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 409 expanded)
%              Number of clauses        :   37 ( 170 expanded)
%              Number of leaves         :    9 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 (1660 expanded)
%              Number of equality atoms :   16 (  93 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',d2_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',t4_subset)).

fof(t25_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( v2_tops_2(X2,X1)
               => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',t25_tops_2)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',d5_xboole_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',t2_subset)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',dt_k7_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',redefinition_k7_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t25_tops_2.p',t6_boole)).

fof(c_0_9,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_tops_2(X11,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(X12,X11)
        | v4_pre_topc(X12,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk4_2(X10,X11),k1_zfmisc_1(u1_struct_0(X10)))
        | v2_tops_2(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk4_2(X10,X11),X11)
        | v2_tops_2(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ l1_pre_topc(X10) )
      & ( ~ v4_pre_topc(esk4_2(X10,X11),X10)
        | v2_tops_2(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

fof(c_0_10,plain,(
    ! [X42,X43,X44] :
      ( ~ r2_hidden(X42,X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X44))
      | m1_subset_1(X42,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( v2_tops_2(X2,X1)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_tops_2])).

cnf(c_0_12,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & v2_tops_2(esk2_0,esk1_0)
    & ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_15,plain,
    ( v4_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v2_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk5_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk5_3(X19,X20,X21),X19)
        | r2_hidden(esk5_3(X19,X20,X21),X20)
        | X21 = k4_xboole_0(X19,X20) )
      & ( r2_hidden(esk5_3(X19,X20,X21),X19)
        | r2_hidden(esk5_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk5_3(X19,X20,X21),X20)
        | r2_hidden(esk5_3(X19,X20,X21),X21)
        | X21 = k4_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_20,plain,(
    ! [X34,X35] :
      ( ~ r2_hidden(X34,X35)
      | m1_subset_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_21,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( v4_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X36,X37)
      | v1_xboole_0(X37)
      | r2_hidden(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | m1_subset_1(k7_subset_1(X23,X24,X25),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_28,negated_conjecture,
    ( v2_tops_2(X1,esk1_0)
    | ~ r2_hidden(esk4_2(esk1_0,X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ r2_hidden(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k7_subset_1(X31,X32,X33) = k4_xboole_0(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_34,negated_conjecture,
    ( v2_tops_2(X1,esk1_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ r2_hidden(esk4_2(esk1_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_35,plain,
    ( r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X2)
    | v2_tops_2(k4_xboole_0(X2,X3),X1)
    | ~ r2_hidden(k4_xboole_0(X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X48] :
      ( ~ v1_xboole_0(X48)
      | X48 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_39,negated_conjecture,
    ( v2_tops_2(k4_xboole_0(esk2_0,X1),esk1_0)
    | ~ r2_hidden(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(k4_xboole_0(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v2_tops_2(k4_xboole_0(esk2_0,X1),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_16])])).

cnf(c_0_44,negated_conjecture,
    ( v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),X1,X2),esk1_0)
    | ~ r2_hidden(esk4_2(esk1_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),X1,X2)),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_tops_2(k4_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_16])])).

cnf(c_0_46,negated_conjecture,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))) = k1_xboole_0
    | v2_tops_2(k4_xboole_0(esk2_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( v2_tops_2(k4_xboole_0(X1,X2),esk1_0)
    | ~ r2_hidden(esk4_2(esk1_0,k4_xboole_0(X1,X2)),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X2,X3))
    | v2_tops_2(k4_xboole_0(X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( v2_tops_2(k4_xboole_0(X1,X2),esk1_0)
    | ~ r2_hidden(esk4_2(esk1_0,k4_xboole_0(X1,X2)),esk2_0)
    | ~ m1_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X2)
    | v2_tops_2(k4_xboole_0(X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( v2_tops_2(k4_xboole_0(esk2_0,X1),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_49]),c_0_53]),c_0_18])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------

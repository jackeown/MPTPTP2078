%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t20_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:36 EDT 2019

% Result     : Theorem 151.26s
% Output     : CNFRefutation 151.26s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 371 expanded)
%              Number of clauses        :   45 ( 156 expanded)
%              Number of leaves         :   10 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  195 (1554 expanded)
%              Number of equality atoms :   13 (  66 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( v1_tops_2(X2,X1)
                  & v1_tops_2(X3,X1) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',t20_tops_2)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',dt_k4_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',redefinition_k4_subset_1)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',d1_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',t4_subset)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',d3_xboole_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',existence_m1_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t20_tops_2.p',t7_boole)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( ( v1_tops_2(X2,X1)
                    & v1_tops_2(X3,X1) )
                 => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tops_2])).

fof(c_0_11,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | m1_subset_1(k4_subset_1(X28,X29,X30),k1_zfmisc_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & v1_tops_2(esk2_0,esk1_0)
    & v1_tops_2(esk3_0,esk1_0)
    & ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | k4_subset_1(X40,X41,X42) = k2_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v1_tops_2(X16,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X17,X16)
        | v3_pre_topc(X17,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk4_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | v1_tops_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk4_2(X15,X16),X16)
        | v1_tops_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ l1_pre_topc(X15) )
      & ( ~ v3_pre_topc(esk4_2(X15,X16),X15)
        | v1_tops_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),X1,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),X1,esk3_0) = k2_xboole_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_21,plain,(
    ! [X50,X51,X52] :
      ( ~ r2_hidden(X50,X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(X52))
      | m1_subset_1(X50,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_22,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X21 != k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | r2_hidden(X23,X21)
        | X21 != k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk5_3(X24,X25,X26),X24)
        | ~ r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k2_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk5_3(X24,X25,X26),X25)
        | ~ r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k2_xboole_0(X24,X25) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X26)
        | r2_hidden(esk5_3(X24,X25,X26),X24)
        | r2_hidden(esk5_3(X24,X25,X26),X25)
        | X26 = k2_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,X1),X1)
    | v1_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_tops_2(k2_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_34,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_35,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | m1_subset_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

fof(c_0_38,plain,(
    ! [X46,X47] :
      ( ~ m1_subset_1(X46,X47)
      | v1_xboole_0(X47)
      | r2_hidden(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_39,plain,(
    ! [X34] : m1_subset_1(esk8_1(X34),X34) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,X2)
    | ~ v1_tops_2(X2,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( v1_tops_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk3_0)
    | r2_hidden(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,plain,(
    ! [X57,X58] :
      ( ~ r2_hidden(X57,X58)
      | ~ v1_xboole_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_19])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk2_0)
    | m1_subset_1(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk8_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ v3_pre_topc(esk4_2(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk1_0)
    | m1_subset_1(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(esk8_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_32])]),c_0_33])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk2_0)
    | r2_hidden(esk8_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( v3_pre_topc(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk1_0)
    | r2_hidden(esk8_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( v1_tops_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk8_1(esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_58]),c_0_32])]),c_0_33])).

cnf(c_0_62,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_59]),c_0_15])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(esk4_2(esk1_0,k2_xboole_0(esk2_0,esk3_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_64]),c_0_32])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------

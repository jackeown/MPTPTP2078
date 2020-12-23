%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:41 EST 2020

% Result     : Theorem 1.05s
% Output     : CNFRefutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 505 expanded)
%              Number of clauses        :   39 ( 167 expanded)
%              Number of leaves         :    9 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  242 (3010 expanded)
%              Number of equality atoms :   19 (  76 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))
                 => m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

fof(t38_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ? [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                  & X4 = X3
                  & r2_hidden(X2,X4)
                  & v3_pre_topc(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t39_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))
              <=> ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(fc7_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k2_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))
                   => m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_waybel_9])).

fof(c_0_10,plain,(
    ! [X28,X29,X30] :
      ( ( m1_subset_1(esk2_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( esk2_3(X28,X29,X30) = X30
        | ~ m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( r2_hidden(X29,esk2_3(X28,X29,X30))
        | ~ m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v3_pre_topc(esk2_3(X28,X29,X30),X28)
        | ~ m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    & m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    & ~ m1_subset_1(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( esk2_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,X1) = X1
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k4_subset_1(X17,X18,X19) = k2_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])])).

cnf(c_0_26,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_23])).

fof(c_0_27,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(X33,X34)
        | ~ r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( v3_pre_topc(X34,X32)
        | ~ r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r2_hidden(X33,X34)
        | ~ v3_pre_topc(X34,X32)
        | r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

fof(c_0_28,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | m1_subset_1(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_29,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | m1_subset_1(k4_subset_1(X14,X15,X16),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_30,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),X1,esk6_0) = k2_xboole_0(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_26]),c_0_23])])).

cnf(c_0_32,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_36,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_25]),c_0_31])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,X1)))
    | ~ v3_pre_topc(k2_xboole_0(esk5_0,esk6_0),esk3_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_44,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,X1)))
    | ~ v3_pre_topc(k2_xboole_0(esk5_0,esk6_0),esk3_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_19]),c_0_22])).

fof(c_0_47,plain,(
    ! [X25,X26,X27] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ v3_pre_topc(X26,X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ v3_pre_topc(X27,X25)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | v3_pre_topc(k2_xboole_0(X26,X27),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).

cnf(c_0_48,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk3_0,esk4_0,X1),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_49,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | m1_subset_1(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))
    | ~ v3_pre_topc(k2_xboole_0(esk5_0,esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( v3_pre_topc(k2_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_19]),c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_23]),c_0_26])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_14]),c_0_15]),c_0_25]),c_0_31])])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.05/1.21  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 1.05/1.21  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 1.05/1.21  #
% 1.05/1.21  # Preprocessing time       : 0.027 s
% 1.05/1.21  # Presaturation interreduction done
% 1.05/1.21  
% 1.05/1.21  # Proof found!
% 1.05/1.21  # SZS status Theorem
% 1.05/1.21  # SZS output start CNFRefutation
% 1.05/1.21  fof(t23_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 1.05/1.21  fof(t38_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&X4=X3)&r2_hidden(X2,X4))&v3_pre_topc(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 1.05/1.21  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.05/1.21  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 1.05/1.21  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.05/1.21  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 1.05/1.21  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.05/1.21  fof(fc7_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k2_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 1.05/1.21  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.05/1.21  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t23_waybel_9])).
% 1.05/1.21  fof(c_0_10, plain, ![X28, X29, X30]:((((m1_subset_1(esk2_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))|~m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(esk2_3(X28,X29,X30)=X30|~m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))))&(r2_hidden(X29,esk2_3(X28,X29,X30))|~m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))))&(v3_pre_topc(esk2_3(X28,X29,X30),X28)|~m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).
% 1.05/1.21  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))&(m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))&~m1_subset_1(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 1.05/1.21  cnf(c_0_12, plain, (esk2_3(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.05/1.21  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.21  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.21  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.21  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.21  cnf(c_0_17, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.05/1.21  cnf(c_0_18, negated_conjecture, (esk2_3(esk3_0,esk4_0,X1)=X1|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 1.05/1.21  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.21  fof(c_0_20, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|~m1_subset_1(X19,k1_zfmisc_1(X17))|k4_subset_1(X17,X18,X19)=k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 1.05/1.21  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 1.05/1.21  cnf(c_0_22, negated_conjecture, (esk2_3(esk3_0,esk4_0,esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.05/1.21  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.21  cnf(c_0_24, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.05/1.21  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19])])).
% 1.05/1.21  cnf(c_0_26, negated_conjecture, (esk2_3(esk3_0,esk4_0,esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_18, c_0_23])).
% 1.05/1.21  fof(c_0_27, plain, ![X32, X33, X34]:(((r2_hidden(X33,X34)|~r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(v3_pre_topc(X34,X32)|~r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32))))&(~r2_hidden(X33,X34)|~v3_pre_topc(X34,X32)|r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 1.05/1.21  fof(c_0_28, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|m1_subset_1(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.05/1.21  fof(c_0_29, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|~m1_subset_1(X16,k1_zfmisc_1(X14))|m1_subset_1(k4_subset_1(X14,X15,X16),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 1.05/1.21  cnf(c_0_30, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),X1,esk6_0)=k2_xboole_0(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.05/1.21  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_26]), c_0_23])])).
% 1.05/1.21  cnf(c_0_32, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.05/1.21  cnf(c_0_33, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.05/1.21  cnf(c_0_34, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.05/1.21  cnf(c_0_35, negated_conjecture, (k4_subset_1(u1_struct_0(esk3_0),esk5_0,esk6_0)=k2_xboole_0(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.05/1.21  fof(c_0_36, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 1.05/1.21  cnf(c_0_37, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_32, c_0_33])).
% 1.05/1.21  cnf(c_0_38, negated_conjecture, (m1_subset_1(k2_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_25]), c_0_31])])).
% 1.05/1.21  cnf(c_0_39, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.05/1.21  cnf(c_0_40, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.05/1.21  cnf(c_0_41, negated_conjecture, (r2_hidden(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,X1)))|~v3_pre_topc(k2_xboole_0(esk5_0,esk6_0),esk3_0)|~r2_hidden(X1,k2_xboole_0(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_14]), c_0_15])]), c_0_16])).
% 1.05/1.21  cnf(c_0_42, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_39])).
% 1.05/1.21  cnf(c_0_43, negated_conjecture, (r2_hidden(esk4_0,esk2_3(esk3_0,esk4_0,X1))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 1.05/1.21  cnf(c_0_44, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.05/1.21  cnf(c_0_45, negated_conjecture, (r2_hidden(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,X1)))|~v3_pre_topc(k2_xboole_0(esk5_0,esk6_0),esk3_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.05/1.21  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_19]), c_0_22])).
% 1.05/1.21  fof(c_0_47, plain, ![X25, X26, X27]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|~v3_pre_topc(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~v3_pre_topc(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|v3_pre_topc(k2_xboole_0(X26,X27),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).
% 1.05/1.21  cnf(c_0_48, negated_conjecture, (v3_pre_topc(esk2_3(esk3_0,esk4_0,X1),esk3_0)|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 1.05/1.21  fof(c_0_49, plain, ![X20, X21]:(~r2_hidden(X20,X21)|m1_subset_1(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 1.05/1.21  cnf(c_0_50, negated_conjecture, (r2_hidden(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))|~v3_pre_topc(k2_xboole_0(esk5_0,esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.05/1.21  cnf(c_0_51, plain, (v3_pre_topc(k2_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.05/1.21  cnf(c_0_52, negated_conjecture, (v3_pre_topc(esk6_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_19]), c_0_22])).
% 1.05/1.21  cnf(c_0_53, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_23]), c_0_26])).
% 1.05/1.21  cnf(c_0_54, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.05/1.21  cnf(c_0_55, negated_conjecture, (r2_hidden(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_14]), c_0_15]), c_0_25]), c_0_31])])).
% 1.05/1.21  cnf(c_0_56, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk5_0,esk6_0),u1_struct_0(k9_yellow_6(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.21  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), ['proof']).
% 1.05/1.21  # SZS output end CNFRefutation
% 1.05/1.21  # Proof object total steps             : 58
% 1.05/1.21  # Proof object clause steps            : 39
% 1.05/1.21  # Proof object formula steps           : 19
% 1.05/1.21  # Proof object conjectures             : 29
% 1.05/1.21  # Proof object clause conjectures      : 26
% 1.05/1.21  # Proof object formula conjectures     : 3
% 1.05/1.21  # Proof object initial clauses used    : 18
% 1.05/1.21  # Proof object initial formulas used   : 9
% 1.05/1.21  # Proof object generating inferences   : 19
% 1.05/1.21  # Proof object simplifying inferences  : 40
% 1.05/1.21  # Training examples: 0 positive, 0 negative
% 1.05/1.21  # Parsed axioms                        : 9
% 1.05/1.21  # Removed by relevancy pruning/SinE    : 0
% 1.05/1.21  # Initial clauses                      : 25
% 1.05/1.21  # Removed in clause preprocessing      : 0
% 1.05/1.21  # Initial clauses in saturation        : 25
% 1.05/1.21  # Processed clauses                    : 2334
% 1.05/1.21  # ...of these trivial                  : 2
% 1.05/1.21  # ...subsumed                          : 788
% 1.05/1.21  # ...remaining for further processing  : 1544
% 1.05/1.21  # Other redundant clauses eliminated   : 3
% 1.05/1.21  # Clauses deleted for lack of memory   : 0
% 1.05/1.21  # Backward-subsumed                    : 0
% 1.05/1.21  # Backward-rewritten                   : 18
% 1.05/1.21  # Generated clauses                    : 89079
% 1.05/1.21  # ...of the previous two non-trivial   : 88937
% 1.05/1.21  # Contextual simplify-reflections      : 2
% 1.05/1.21  # Paramodulations                      : 88890
% 1.05/1.21  # Factorizations                       : 186
% 1.05/1.21  # Equation resolutions                 : 3
% 1.05/1.21  # Propositional unsat checks           : 0
% 1.05/1.21  #    Propositional check models        : 0
% 1.05/1.21  #    Propositional check unsatisfiable : 0
% 1.05/1.21  #    Propositional clauses             : 0
% 1.05/1.21  #    Propositional clauses after purity: 0
% 1.05/1.21  #    Propositional unsat core size     : 0
% 1.05/1.21  #    Propositional preprocessing time  : 0.000
% 1.05/1.21  #    Propositional encoding time       : 0.000
% 1.05/1.21  #    Propositional solver time         : 0.000
% 1.05/1.21  #    Success case prop preproc time    : 0.000
% 1.05/1.21  #    Success case prop encoding time   : 0.000
% 1.05/1.21  #    Success case prop solver time     : 0.000
% 1.05/1.21  # Current number of processed clauses  : 1498
% 1.05/1.21  #    Positive orientable unit clauses  : 728
% 1.05/1.21  #    Positive unorientable unit clauses: 0
% 1.05/1.21  #    Negative unit clauses             : 2
% 1.05/1.21  #    Non-unit-clauses                  : 768
% 1.05/1.21  # Current number of unprocessed clauses: 86650
% 1.05/1.21  # ...number of literals in the above   : 276944
% 1.05/1.21  # Current number of archived formulas  : 0
% 1.05/1.21  # Current number of archived clauses   : 43
% 1.05/1.21  # Clause-clause subsumption calls (NU) : 261776
% 1.05/1.21  # Rec. Clause-clause subsumption calls : 131022
% 1.05/1.21  # Non-unit clause-clause subsumptions  : 790
% 1.05/1.21  # Unit Clause-clause subsumption calls : 7393
% 1.05/1.21  # Rewrite failures with RHS unbound    : 0
% 1.05/1.21  # BW rewrite match attempts            : 19804
% 1.05/1.21  # BW rewrite match successes           : 13
% 1.05/1.21  # Condensation attempts                : 0
% 1.05/1.21  # Condensation successes               : 0
% 1.05/1.21  # Termbank termtop insertions          : 2341208
% 1.05/1.22  
% 1.05/1.22  # -------------------------------------------------
% 1.05/1.22  # User time                : 0.820 s
% 1.05/1.22  # System time              : 0.052 s
% 1.05/1.22  # Total time               : 0.872 s
% 1.05/1.22  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:41 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 455 expanded)
%              Number of clauses        :   52 ( 159 expanded)
%              Number of leaves         :    8 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          :  269 (2579 expanded)
%              Number of equality atoms :   15 (  65 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   24 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(fc7_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k2_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X28,X29,X30] :
      ( ( m1_subset_1(esk3_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( esk3_3(X28,X29,X30) = X30
        | ~ m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( r2_hidden(X29,esk3_3(X28,X29,X30))
        | ~ m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v3_pre_topc(esk3_3(X28,X29,X30),X28)
        | ~ m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    & m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    & ~ m1_subset_1(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( esk3_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,X1) = X1
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

fof(c_0_24,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18])])).

fof(c_0_27,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_23]),c_0_19])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_39,plain,(
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

fof(c_0_40,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | m1_subset_1(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk1_2(X1,u1_struct_0(esk4_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk1_2(X1,u1_struct_0(esk4_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | r2_hidden(esk1_2(k2_xboole_0(esk6_0,X1),u1_struct_0(esk4_0)),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_32])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,esk3_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,X1)))
    | ~ v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_55,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,X1)))
    | ~ v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_19]),c_0_23])).

fof(c_0_58,plain,(
    ! [X25,X26,X27] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ v3_pre_topc(X26,X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ v3_pre_topc(X27,X25)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | v3_pre_topc(k2_xboole_0(X26,X27),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(esk3_3(esk4_0,esk5_0,X1),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_38]),c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    | ~ v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( v3_pre_topc(k2_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_19]),c_0_23])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_18]),c_0_22])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_13]),c_0_14]),c_0_28]),c_0_26])])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:36:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 2.13/2.30  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 2.13/2.30  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 2.13/2.30  #
% 2.13/2.30  # Preprocessing time       : 0.018 s
% 2.13/2.30  # Presaturation interreduction done
% 2.13/2.30  
% 2.13/2.30  # Proof found!
% 2.13/2.30  # SZS status Theorem
% 2.13/2.30  # SZS output start CNFRefutation
% 2.13/2.30  fof(t23_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 2.13/2.30  fof(t38_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&X4=X3)&r2_hidden(X2,X4))&v3_pre_topc(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 2.13/2.30  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.13/2.30  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.13/2.30  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.13/2.30  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 2.13/2.30  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.13/2.30  fof(fc7_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k2_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 2.13/2.30  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t23_waybel_9])).
% 2.13/2.30  fof(c_0_9, plain, ![X28, X29, X30]:((((m1_subset_1(esk3_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))|~m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(esk3_3(X28,X29,X30)=X30|~m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))))&(r2_hidden(X29,esk3_3(X28,X29,X30))|~m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))))&(v3_pre_topc(esk3_3(X28,X29,X30),X28)|~m1_subset_1(X30,u1_struct_0(k9_yellow_6(X28,X29)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).
% 2.13/2.30  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))&(m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))&~m1_subset_1(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 2.13/2.30  cnf(c_0_11, plain, (esk3_3(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.13/2.30  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.13/2.30  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.13/2.30  cnf(c_0_14, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.13/2.30  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.13/2.30  cnf(c_0_16, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.13/2.30  cnf(c_0_17, negated_conjecture, (esk3_3(esk4_0,esk5_0,X1)=X1|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 2.13/2.30  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.13/2.30  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.13/2.30  fof(c_0_20, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.13/2.30  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 2.13/2.30  cnf(c_0_22, negated_conjecture, (esk3_3(esk4_0,esk5_0,esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 2.13/2.30  cnf(c_0_23, negated_conjecture, (esk3_3(esk4_0,esk5_0,esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 2.13/2.30  fof(c_0_24, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.13/2.30  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.13/2.30  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_18])])).
% 2.13/2.30  fof(c_0_27, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 2.13/2.30  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_23]), c_0_19])])).
% 2.13/2.30  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.13/2.30  cnf(c_0_30, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 2.13/2.30  cnf(c_0_31, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.13/2.30  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.13/2.30  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.13/2.30  cnf(c_0_34, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 2.13/2.30  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.13/2.30  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 2.13/2.30  cnf(c_0_37, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_31])).
% 2.13/2.30  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 2.13/2.30  fof(c_0_39, plain, ![X32, X33, X34]:(((r2_hidden(X33,X34)|~r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(v3_pre_topc(X34,X32)|~r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32))))&(~r2_hidden(X33,X34)|~v3_pre_topc(X34,X32)|r2_hidden(X34,u1_struct_0(k9_yellow_6(X32,X33)))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 2.13/2.30  fof(c_0_40, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|m1_subset_1(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 2.13/2.30  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_34])).
% 2.13/2.30  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk4_0))|~r2_hidden(esk1_2(X1,u1_struct_0(esk4_0)),esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.13/2.30  cnf(c_0_43, plain, (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))|r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)|r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.13/2.30  cnf(c_0_44, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.13/2.30  cnf(c_0_45, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.13/2.30  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk4_0))|~r2_hidden(esk1_2(X1,u1_struct_0(esk4_0)),esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_41])).
% 2.13/2.30  cnf(c_0_47, negated_conjecture, (m1_subset_1(k2_xboole_0(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|r2_hidden(esk1_2(k2_xboole_0(esk6_0,X1),u1_struct_0(esk4_0)),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_32])).
% 2.13/2.30  cnf(c_0_48, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_44, c_0_45])).
% 2.13/2.30  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_xboole_0(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32])).
% 2.13/2.30  cnf(c_0_50, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.13/2.30  cnf(c_0_51, plain, (r2_hidden(X1,esk3_3(X2,X1,X3))|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.13/2.30  cnf(c_0_52, negated_conjecture, (r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,X1)))|~v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)|~r2_hidden(X1,k2_xboole_0(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_13]), c_0_14])]), c_0_15])).
% 2.13/2.30  cnf(c_0_53, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_50])).
% 2.13/2.30  cnf(c_0_54, negated_conjecture, (r2_hidden(esk5_0,esk3_3(esk4_0,esk5_0,X1))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 2.13/2.30  cnf(c_0_55, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.13/2.30  cnf(c_0_56, negated_conjecture, (r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,X1)))|~v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 2.13/2.30  cnf(c_0_57, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_19]), c_0_23])).
% 2.13/2.30  fof(c_0_58, plain, ![X25, X26, X27]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|~v3_pre_topc(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|~v3_pre_topc(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|v3_pre_topc(k2_xboole_0(X26,X27),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).
% 2.13/2.30  cnf(c_0_59, negated_conjecture, (v3_pre_topc(esk3_3(esk4_0,esk5_0,X1),esk4_0)|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 2.13/2.30  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_38]), c_0_32])).
% 2.13/2.30  cnf(c_0_61, negated_conjecture, (r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))|~v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.13/2.30  cnf(c_0_62, plain, (v3_pre_topc(k2_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.13/2.30  cnf(c_0_63, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_19]), c_0_23])).
% 2.13/2.30  cnf(c_0_64, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_18]), c_0_22])).
% 2.13/2.30  cnf(c_0_65, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_60])).
% 2.13/2.30  cnf(c_0_66, negated_conjecture, (r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64]), c_0_13]), c_0_14]), c_0_28]), c_0_26])])).
% 2.13/2.30  cnf(c_0_67, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.13/2.30  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), ['proof']).
% 2.13/2.30  # SZS output end CNFRefutation
% 2.13/2.30  # Proof object total steps             : 69
% 2.13/2.30  # Proof object clause steps            : 52
% 2.13/2.30  # Proof object formula steps           : 17
% 2.13/2.30  # Proof object conjectures             : 34
% 2.13/2.30  # Proof object clause conjectures      : 31
% 2.13/2.30  # Proof object formula conjectures     : 3
% 2.13/2.30  # Proof object initial clauses used    : 21
% 2.13/2.30  # Proof object initial formulas used   : 8
% 2.13/2.30  # Proof object generating inferences   : 28
% 2.13/2.30  # Proof object simplifying inferences  : 41
% 2.13/2.30  # Training examples: 0 positive, 0 negative
% 2.13/2.30  # Parsed axioms                        : 8
% 2.13/2.30  # Removed by relevancy pruning/SinE    : 0
% 2.13/2.30  # Initial clauses                      : 27
% 2.13/2.30  # Removed in clause preprocessing      : 0
% 2.13/2.30  # Initial clauses in saturation        : 27
% 2.13/2.30  # Processed clauses                    : 3509
% 2.13/2.30  # ...of these trivial                  : 51
% 2.13/2.30  # ...subsumed                          : 1557
% 2.13/2.30  # ...remaining for further processing  : 1901
% 2.13/2.30  # Other redundant clauses eliminated   : 3
% 2.13/2.30  # Clauses deleted for lack of memory   : 0
% 2.13/2.30  # Backward-subsumed                    : 86
% 2.13/2.30  # Backward-rewritten                   : 120
% 2.13/2.30  # Generated clauses                    : 300178
% 2.13/2.30  # ...of the previous two non-trivial   : 257391
% 2.13/2.30  # Contextual simplify-reflections      : 52
% 2.13/2.30  # Paramodulations                      : 299907
% 2.13/2.30  # Factorizations                       : 268
% 2.13/2.30  # Equation resolutions                 : 3
% 2.13/2.30  # Propositional unsat checks           : 0
% 2.13/2.30  #    Propositional check models        : 0
% 2.13/2.30  #    Propositional check unsatisfiable : 0
% 2.13/2.30  #    Propositional clauses             : 0
% 2.13/2.30  #    Propositional clauses after purity: 0
% 2.13/2.30  #    Propositional unsat core size     : 0
% 2.13/2.30  #    Propositional preprocessing time  : 0.000
% 2.13/2.30  #    Propositional encoding time       : 0.000
% 2.13/2.30  #    Propositional solver time         : 0.000
% 2.13/2.30  #    Success case prop preproc time    : 0.000
% 2.13/2.30  #    Success case prop encoding time   : 0.000
% 2.13/2.30  #    Success case prop solver time     : 0.000
% 2.13/2.30  # Current number of processed clauses  : 1665
% 2.13/2.30  #    Positive orientable unit clauses  : 165
% 2.13/2.30  #    Positive unorientable unit clauses: 0
% 2.13/2.30  #    Negative unit clauses             : 2
% 2.13/2.30  #    Non-unit-clauses                  : 1498
% 2.13/2.30  # Current number of unprocessed clauses: 253830
% 2.13/2.30  # ...number of literals in the above   : 1084086
% 2.13/2.30  # Current number of archived formulas  : 0
% 2.13/2.30  # Current number of archived clauses   : 233
% 2.13/2.30  # Clause-clause subsumption calls (NU) : 962380
% 2.13/2.30  # Rec. Clause-clause subsumption calls : 547651
% 2.13/2.30  # Non-unit clause-clause subsumptions  : 1612
% 2.13/2.30  # Unit Clause-clause subsumption calls : 57804
% 2.13/2.30  # Rewrite failures with RHS unbound    : 0
% 2.13/2.30  # BW rewrite match attempts            : 1661
% 2.13/2.30  # BW rewrite match successes           : 13
% 2.13/2.30  # Condensation attempts                : 0
% 2.13/2.30  # Condensation successes               : 0
% 2.13/2.30  # Termbank termtop insertions          : 6045191
% 2.13/2.31  
% 2.13/2.31  # -------------------------------------------------
% 2.13/2.31  # User time                : 1.895 s
% 2.13/2.31  # System time              : 0.085 s
% 2.13/2.31  # Total time               : 1.979 s
% 2.13/2.31  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

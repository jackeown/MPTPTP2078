%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:42 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 456 expanded)
%              Number of clauses        :   51 ( 160 expanded)
%              Number of leaves         :   10 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  283 (2536 expanded)
%              Number of equality atoms :   14 (  57 expanded)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

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

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X31,X32,X33] :
      ( ( m1_subset_1(esk3_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X33,u1_struct_0(k9_yellow_6(X31,X32)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( esk3_3(X31,X32,X33) = X33
        | ~ m1_subset_1(X33,u1_struct_0(k9_yellow_6(X31,X32)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(X32,esk3_3(X31,X32,X33))
        | ~ m1_subset_1(X33,u1_struct_0(k9_yellow_6(X31,X32)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v3_pre_topc(esk3_3(X31,X32,X33),X31)
        | ~ m1_subset_1(X33,u1_struct_0(k9_yellow_6(X31,X32)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    & m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    & ~ m1_subset_1(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_13,plain,
    ( esk3_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,X1) = X1
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X17)
      | r1_tarski(k2_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_20])])).

cnf(c_0_31,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

fof(c_0_32,plain,(
    ! [X19,X20,X21] :
      ( ( m1_subset_1(esk2_3(X19,X20,X21),X19)
        | r1_tarski(X20,X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(X19)) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | r1_tarski(X20,X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(X19)) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | r1_tarski(X20,X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X35,X36,X37] :
      ( ( r2_hidden(X36,X37)
        | ~ r2_hidden(X37,u1_struct_0(k9_yellow_6(X35,X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( v3_pre_topc(X37,X35)
        | ~ r2_hidden(X37,u1_struct_0(k9_yellow_6(X35,X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r2_hidden(X36,X37)
        | ~ v3_pre_topc(X37,X35)
        | r2_hidden(X37,u1_struct_0(k9_yellow_6(X35,X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

fof(c_0_35,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | m1_subset_1(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_31]),c_0_25])])).

cnf(c_0_39,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(X1,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

fof(c_0_45,plain,(
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

cnf(c_0_46,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))
    | ~ r2_hidden(esk2_3(k2_xboole_0(X2,X3),X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,esk3_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_3(k2_xboole_0(X2,X3),X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_40])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1)
    | ~ r2_hidden(esk2_3(k2_xboole_0(X1,X2),X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,X1)))
    | ~ v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_57,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,X1)))
    | ~ v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_20]),c_0_24])).

fof(c_0_61,plain,(
    ! [X28,X29,X30] :
      ( ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ v3_pre_topc(X29,X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ v3_pre_topc(X30,X28)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
      | v3_pre_topc(k2_xboole_0(X29,X30),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).

cnf(c_0_62,negated_conjecture,
    ( v3_pre_topc(esk3_3(esk4_0,esk5_0,X1),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    | ~ v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( v3_pre_topc(k2_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_20]),c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_25]),c_0_31])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_15]),c_0_16]),c_0_30]),c_0_38])])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.14/5.33  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 5.14/5.33  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 5.14/5.33  #
% 5.14/5.33  # Preprocessing time       : 0.028 s
% 5.14/5.33  # Presaturation interreduction done
% 5.14/5.33  
% 5.14/5.33  # Proof found!
% 5.14/5.33  # SZS status Theorem
% 5.14/5.33  # SZS output start CNFRefutation
% 5.14/5.33  fof(t23_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 5.14/5.33  fof(t38_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&X4=X3)&r2_hidden(X2,X4))&v3_pre_topc(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 5.14/5.33  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.14/5.33  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.14/5.33  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.14/5.33  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 5.14/5.33  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 5.14/5.33  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.14/5.33  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.14/5.33  fof(fc7_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k2_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 5.14/5.33  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k2_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t23_waybel_9])).
% 5.14/5.33  fof(c_0_11, plain, ![X31, X32, X33]:((((m1_subset_1(esk3_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X33,u1_struct_0(k9_yellow_6(X31,X32)))|~m1_subset_1(X32,u1_struct_0(X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(esk3_3(X31,X32,X33)=X33|~m1_subset_1(X33,u1_struct_0(k9_yellow_6(X31,X32)))|~m1_subset_1(X32,u1_struct_0(X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))))&(r2_hidden(X32,esk3_3(X31,X32,X33))|~m1_subset_1(X33,u1_struct_0(k9_yellow_6(X31,X32)))|~m1_subset_1(X32,u1_struct_0(X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))))&(v3_pre_topc(esk3_3(X31,X32,X33),X31)|~m1_subset_1(X33,u1_struct_0(k9_yellow_6(X31,X32)))|~m1_subset_1(X32,u1_struct_0(X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).
% 5.14/5.33  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))&(m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))&~m1_subset_1(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 5.14/5.33  cnf(c_0_13, plain, (esk3_3(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.14/5.33  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.14/5.33  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.14/5.33  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.14/5.33  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.14/5.33  cnf(c_0_18, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.14/5.33  cnf(c_0_19, negated_conjecture, (esk3_3(esk4_0,esk5_0,X1)=X1|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.14/5.33  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.14/5.33  fof(c_0_21, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 5.14/5.33  fof(c_0_22, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X18,X17)|r1_tarski(k2_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 5.14/5.33  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.14/5.33  cnf(c_0_24, negated_conjecture, (esk3_3(esk4_0,esk5_0,esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 5.14/5.33  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.14/5.33  fof(c_0_26, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 5.14/5.33  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.14/5.33  cnf(c_0_28, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.14/5.33  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.14/5.33  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_20])])).
% 5.14/5.33  cnf(c_0_31, negated_conjecture, (esk3_3(esk4_0,esk5_0,esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_19, c_0_25])).
% 5.14/5.33  fof(c_0_32, plain, ![X19, X20, X21]:((m1_subset_1(esk2_3(X19,X20,X21),X19)|r1_tarski(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(X19)))&((r2_hidden(esk2_3(X19,X20,X21),X20)|r1_tarski(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(X19)))&(~r2_hidden(esk2_3(X19,X20,X21),X21)|r1_tarski(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 5.14/5.33  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 5.14/5.33  fof(c_0_34, plain, ![X35, X36, X37]:(((r2_hidden(X36,X37)|~r2_hidden(X37,u1_struct_0(k9_yellow_6(X35,X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(v3_pre_topc(X37,X35)|~r2_hidden(X37,u1_struct_0(k9_yellow_6(X35,X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35))))&(~r2_hidden(X36,X37)|~v3_pre_topc(X37,X35)|r2_hidden(X37,u1_struct_0(k9_yellow_6(X35,X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 5.14/5.33  fof(c_0_35, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(X27))|m1_subset_1(X25,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 5.14/5.33  cnf(c_0_36, plain, (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 5.14/5.33  cnf(c_0_37, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 5.14/5.33  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_31]), c_0_25])])).
% 5.14/5.33  cnf(c_0_39, plain, (r1_tarski(X2,X3)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.14/5.33  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_27, c_0_33])).
% 5.14/5.33  cnf(c_0_41, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 5.14/5.33  cnf(c_0_42, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 5.14/5.33  cnf(c_0_43, negated_conjecture, (m1_subset_1(k2_xboole_0(X1,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_tarski(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 5.14/5.33  cnf(c_0_44, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 5.14/5.33  fof(c_0_45, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 5.14/5.33  cnf(c_0_46, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.14/5.33  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))|~r2_hidden(esk2_3(k2_xboole_0(X2,X3),X1,X2),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 5.14/5.33  cnf(c_0_48, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_41, c_0_42])).
% 5.14/5.33  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_xboole_0(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 5.14/5.33  cnf(c_0_50, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 5.14/5.33  cnf(c_0_51, plain, (r2_hidden(X1,esk3_3(X2,X1,X3))|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.14/5.33  cnf(c_0_52, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_3(k2_xboole_0(X2,X3),X1,X2),X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_46, c_0_40])).
% 5.14/5.33  cnf(c_0_53, plain, (r1_tarski(X1,X1)|~r2_hidden(esk2_3(k2_xboole_0(X1,X2),X1,X1),X1)), inference(spm,[status(thm)],[c_0_47, c_0_40])).
% 5.14/5.33  cnf(c_0_54, negated_conjecture, (r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,X1)))|~v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)|~r2_hidden(X1,k2_xboole_0(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_15]), c_0_16])]), c_0_17])).
% 5.14/5.33  cnf(c_0_55, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_50])).
% 5.14/5.33  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_0,esk3_3(esk4_0,esk5_0,X1))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.14/5.33  cnf(c_0_57, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.14/5.33  cnf(c_0_58, plain, (r1_tarski(X1,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_40]), c_0_53])).
% 5.14/5.33  cnf(c_0_59, negated_conjecture, (r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,X1)))|~v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 5.14/5.33  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_20]), c_0_24])).
% 5.14/5.33  fof(c_0_61, plain, ![X28, X29, X30]:(~v2_pre_topc(X28)|~l1_pre_topc(X28)|~v3_pre_topc(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~v3_pre_topc(X30,X28)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|v3_pre_topc(k2_xboole_0(X29,X30),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_tops_1])])).
% 5.14/5.33  cnf(c_0_62, negated_conjecture, (v3_pre_topc(esk3_3(esk4_0,esk5_0,X1),esk4_0)|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 5.14/5.33  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_58])).
% 5.14/5.33  cnf(c_0_64, negated_conjecture, (r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))|~v3_pre_topc(k2_xboole_0(esk6_0,esk7_0),esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 5.14/5.33  cnf(c_0_65, plain, (v3_pre_topc(k2_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 5.14/5.33  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_20]), c_0_24])).
% 5.14/5.33  cnf(c_0_67, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_25]), c_0_31])).
% 5.14/5.33  cnf(c_0_68, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_63])).
% 5.14/5.33  cnf(c_0_69, negated_conjecture, (r2_hidden(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), c_0_15]), c_0_16]), c_0_30]), c_0_38])])).
% 5.14/5.33  cnf(c_0_70, negated_conjecture, (~m1_subset_1(k2_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 5.14/5.33  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), ['proof']).
% 5.14/5.33  # SZS output end CNFRefutation
% 5.14/5.33  # Proof object total steps             : 72
% 5.14/5.33  # Proof object clause steps            : 51
% 5.14/5.33  # Proof object formula steps           : 21
% 5.14/5.33  # Proof object conjectures             : 30
% 5.14/5.33  # Proof object clause conjectures      : 27
% 5.14/5.33  # Proof object formula conjectures     : 3
% 5.14/5.33  # Proof object initial clauses used    : 21
% 5.14/5.33  # Proof object initial formulas used   : 10
% 5.14/5.33  # Proof object generating inferences   : 28
% 5.14/5.33  # Proof object simplifying inferences  : 38
% 5.14/5.33  # Training examples: 0 positive, 0 negative
% 5.14/5.33  # Parsed axioms                        : 10
% 5.14/5.33  # Removed by relevancy pruning/SinE    : 0
% 5.14/5.33  # Initial clauses                      : 29
% 5.14/5.33  # Removed in clause preprocessing      : 0
% 5.14/5.33  # Initial clauses in saturation        : 29
% 5.14/5.33  # Processed clauses                    : 7091
% 5.14/5.33  # ...of these trivial                  : 275
% 5.14/5.33  # ...subsumed                          : 2116
% 5.14/5.33  # ...remaining for further processing  : 4700
% 5.14/5.33  # Other redundant clauses eliminated   : 3
% 5.14/5.33  # Clauses deleted for lack of memory   : 0
% 5.14/5.33  # Backward-subsumed                    : 5
% 5.14/5.33  # Backward-rewritten                   : 45
% 5.14/5.33  # Generated clauses                    : 668672
% 5.14/5.33  # ...of the previous two non-trivial   : 666345
% 5.14/5.33  # Contextual simplify-reflections      : 5
% 5.14/5.33  # Paramodulations                      : 668343
% 5.14/5.33  # Factorizations                       : 326
% 5.14/5.33  # Equation resolutions                 : 3
% 5.14/5.33  # Propositional unsat checks           : 0
% 5.14/5.33  #    Propositional check models        : 0
% 5.14/5.33  #    Propositional check unsatisfiable : 0
% 5.14/5.33  #    Propositional clauses             : 0
% 5.14/5.33  #    Propositional clauses after purity: 0
% 5.14/5.33  #    Propositional unsat core size     : 0
% 5.14/5.33  #    Propositional preprocessing time  : 0.000
% 5.14/5.33  #    Propositional encoding time       : 0.000
% 5.14/5.33  #    Propositional solver time         : 0.000
% 5.14/5.33  #    Success case prop preproc time    : 0.000
% 5.14/5.33  #    Success case prop encoding time   : 0.000
% 5.14/5.33  #    Success case prop solver time     : 0.000
% 5.14/5.33  # Current number of processed clauses  : 4618
% 5.14/5.33  #    Positive orientable unit clauses  : 2706
% 5.14/5.33  #    Positive unorientable unit clauses: 0
% 5.14/5.33  #    Negative unit clauses             : 2
% 5.14/5.33  #    Non-unit-clauses                  : 1910
% 5.14/5.33  # Current number of unprocessed clauses: 658982
% 5.14/5.33  # ...number of literals in the above   : 1787151
% 5.14/5.33  # Current number of archived formulas  : 0
% 5.14/5.33  # Current number of archived clauses   : 79
% 5.14/5.33  # Clause-clause subsumption calls (NU) : 1002643
% 5.14/5.33  # Rec. Clause-clause subsumption calls : 746030
% 5.14/5.33  # Non-unit clause-clause subsumptions  : 2123
% 5.14/5.33  # Unit Clause-clause subsumption calls : 227570
% 5.14/5.33  # Rewrite failures with RHS unbound    : 0
% 5.14/5.33  # BW rewrite match attempts            : 396207
% 5.14/5.33  # BW rewrite match successes           : 29
% 5.14/5.33  # Condensation attempts                : 0
% 5.14/5.33  # Condensation successes               : 0
% 5.14/5.33  # Termbank termtop insertions          : 20712724
% 5.14/5.37  
% 5.14/5.37  # -------------------------------------------------
% 5.14/5.37  # User time                : 4.648 s
% 5.14/5.37  # System time              : 0.378 s
% 5.14/5.37  # Total time               : 5.026 s
% 5.14/5.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

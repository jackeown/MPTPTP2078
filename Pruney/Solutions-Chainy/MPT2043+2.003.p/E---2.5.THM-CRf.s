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
% DateTime   : Thu Dec  3 11:21:49 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 283 expanded)
%              Number of clauses        :   66 ( 144 expanded)
%              Number of leaves         :   14 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  270 ( 862 expanded)
%              Number of equality atoms :   49 ( 202 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_yellow19,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t11_waybel_7,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
     => ( v13_waybel_0(X2,k3_yellow_1(X1))
      <=> ! [X3,X4] :
            ( ( r1_tarski(X3,X4)
              & r1_tarski(X4,X1)
              & r2_hidden(X3,X2) )
           => r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
              & v2_waybel_0(X2,k3_yellow_1(X1))
              & v13_waybel_0(X2,k3_yellow_1(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
           => ! [X3] :
                ~ ( r2_hidden(X3,X2)
                  & v1_xboole_0(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_yellow19])).

fof(c_0_15,plain,(
    ! [X34] : k3_yellow_1(X34) = k2_yellow_1(k9_setfam_1(X34)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_16,plain,(
    ! [X32] : k9_setfam_1(X32) = k1_zfmisc_1(X32) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_17,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0)
    & ~ v1_xboole_0(esk7_0)
    & v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0)))
    & v2_waybel_0(esk7_0,k3_yellow_1(esk6_0))
    & v13_waybel_0(esk7_0,k3_yellow_1(esk6_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0))))
    & r2_hidden(esk8_0,esk7_0)
    & v1_xboole_0(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_19,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X18,X17)
        | r1_tarski(X18,X16)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r1_tarski(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X21)
        | ~ r1_tarski(esk3_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) )
      & ( r2_hidden(esk3_2(X20,X21),X21)
        | r1_tarski(esk3_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X33] :
      ( u1_struct_0(k2_yellow_1(X33)) = X33
      & u1_orders_2(k2_yellow_1(X33)) = k1_yellow_1(X33) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_26,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_27,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk6_0))))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ v13_waybel_0(X38,k3_yellow_1(X37))
        | ~ r1_tarski(X39,X40)
        | ~ r1_tarski(X40,X37)
        | ~ r2_hidden(X39,X38)
        | r2_hidden(X40,X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37)))) )
      & ( r1_tarski(esk4_2(X37,X38),esk5_2(X37,X38))
        | v13_waybel_0(X38,k3_yellow_1(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37)))) )
      & ( r1_tarski(esk5_2(X37,X38),X37)
        | v13_waybel_0(X38,k3_yellow_1(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37)))) )
      & ( r2_hidden(esk4_2(X37,X38),X38)
        | v13_waybel_0(X38,k3_yellow_1(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37)))) )
      & ( ~ r2_hidden(esk5_2(X37,X38),X38)
        | v13_waybel_0(X38,k3_yellow_1(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).

fof(c_0_42,plain,(
    ! [X23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_38])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_49,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,k3_yellow_1(X2))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_53,plain,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(esk2_2(X11,X12),X11)
        | ~ r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(k1_zfmisc_1(X3),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_47])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_40])).

cnf(c_0_56,plain,
    ( r2_hidden(X4,X1)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r2_hidden(X3,X1)
    | ~ v13_waybel_0(X1,k2_yellow_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_24]),c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( v13_waybel_0(esk7_0,k3_yellow_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_50])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_52])).

cnf(c_0_63,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | k1_zfmisc_1(k1_zfmisc_1(X3)) != k1_zfmisc_1(k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,k2_yellow_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ r2_hidden(X4,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X4,X1) ),
    inference(rw,[status(thm)],[c_0_56,c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( v13_waybel_0(esk7_0,k2_yellow_1(k1_zfmisc_1(esk6_0))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_24])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( esk7_0 = X1
    | r2_hidden(esk2_2(esk7_0,X1),X1)
    | r2_hidden(esk2_2(esk7_0,X1),X2)
    | X2 != k1_zfmisc_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,X2)
    | k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X1))) != k1_zfmisc_1(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_40])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_38])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( esk7_0 = X1
    | r2_hidden(esk2_2(esk7_0,X1),k1_zfmisc_1(esk6_0))
    | r2_hidden(esk2_2(esk7_0,X1),X1) ),
    inference(er,[status(thm)],[c_0_70])).

fof(c_0_77,plain,(
    ! [X35,X36] :
      ( ( ~ v1_subset_1(X36,X35)
        | X36 != X35
        | ~ m1_subset_1(X36,k1_zfmisc_1(X35)) )
      & ( X36 = X35
        | v1_subset_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,X2)
    | k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X3))) != k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_hidden(X2,esk7_0)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_83,negated_conjecture,
    ( k1_zfmisc_1(esk6_0) = esk7_0
    | r2_hidden(esk2_2(esk7_0,k1_zfmisc_1(esk6_0)),k1_zfmisc_1(esk6_0)) ),
    inference(ef,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,X2)
    | k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X1)))) != k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_40])).

cnf(c_0_86,negated_conjecture,
    ( v1_subset_1(esk7_0,u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_24])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_59]),c_0_81])])).

cnf(c_0_88,negated_conjecture,
    ( k1_zfmisc_1(esk6_0) = esk7_0
    | ~ r2_hidden(esk2_2(esk7_0,k1_zfmisc_1(esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_90,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( v1_subset_1(esk7_0,k1_zfmisc_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_32])).

cnf(c_0_92,negated_conjecture,
    ( k1_zfmisc_1(esk6_0) = esk7_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_83]),c_0_88])).

cnf(c_0_93,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92]),c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.50/0.66  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.50/0.66  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.50/0.66  #
% 0.50/0.66  # Preprocessing time       : 0.029 s
% 0.50/0.66  
% 0.50/0.66  # Proof found!
% 0.50/0.66  # SZS status Theorem
% 0.50/0.66  # SZS output start CNFRefutation
% 0.50/0.66  fof(t2_yellow19, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 0.50/0.66  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.50/0.66  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.50/0.66  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.50/0.66  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.50/0.66  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.50/0.66  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.50/0.66  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.50/0.66  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.50/0.66  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.50/0.66  fof(t11_waybel_7, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))=>(v13_waybel_0(X2,k3_yellow_1(X1))<=>![X3, X4]:(((r1_tarski(X3,X4)&r1_tarski(X4,X1))&r2_hidden(X3,X2))=>r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_waybel_7)).
% 0.50/0.66  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.50/0.66  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.50/0.66  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.50/0.66  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3)))))), inference(assume_negation,[status(cth)],[t2_yellow19])).
% 0.50/0.66  fof(c_0_15, plain, ![X34]:k3_yellow_1(X34)=k2_yellow_1(k9_setfam_1(X34)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.50/0.66  fof(c_0_16, plain, ![X32]:k9_setfam_1(X32)=k1_zfmisc_1(X32), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.50/0.66  fof(c_0_17, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.50/0.66  fof(c_0_18, negated_conjecture, (~v1_xboole_0(esk6_0)&(((((~v1_xboole_0(esk7_0)&v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0))))&v2_waybel_0(esk7_0,k3_yellow_1(esk6_0)))&v13_waybel_0(esk7_0,k3_yellow_1(esk6_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0)))))&(r2_hidden(esk8_0,esk7_0)&v1_xboole_0(esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.50/0.66  cnf(c_0_19, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.66  cnf(c_0_20, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.50/0.66  fof(c_0_21, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X18,X17)|r1_tarski(X18,X16)|X17!=k1_zfmisc_1(X16))&(~r1_tarski(X19,X16)|r2_hidden(X19,X17)|X17!=k1_zfmisc_1(X16)))&((~r2_hidden(esk3_2(X20,X21),X21)|~r1_tarski(esk3_2(X20,X21),X20)|X21=k1_zfmisc_1(X20))&(r2_hidden(esk3_2(X20,X21),X21)|r1_tarski(esk3_2(X20,X21),X20)|X21=k1_zfmisc_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.50/0.66  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.66  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.66  cnf(c_0_24, plain, (k3_yellow_1(X1)=k2_yellow_1(k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.50/0.66  fof(c_0_25, plain, ![X33]:(u1_struct_0(k2_yellow_1(X33))=X33&u1_orders_2(k2_yellow_1(X33))=k1_yellow_1(X33)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.50/0.66  fof(c_0_26, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|m1_subset_1(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.50/0.66  fof(c_0_27, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.50/0.66  cnf(c_0_28, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.66  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.50/0.66  fof(c_0_30, plain, ![X29, X30, X31]:(~r2_hidden(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(X31))|~v1_xboole_0(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.50/0.66  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk6_0)))))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.50/0.66  cnf(c_0_32, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.50/0.66  cnf(c_0_33, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.50/0.66  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.50/0.66  cnf(c_0_35, plain, (r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.50/0.66  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.50/0.66  fof(c_0_37, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.50/0.66  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(esk6_0)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.50/0.66  cnf(c_0_39, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.50/0.66  cnf(c_0_40, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_35])).
% 0.50/0.66  fof(c_0_41, plain, ![X37, X38, X39, X40]:((~v13_waybel_0(X38,k3_yellow_1(X37))|(~r1_tarski(X39,X40)|~r1_tarski(X40,X37)|~r2_hidden(X39,X38)|r2_hidden(X40,X38))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37)))))&((((r1_tarski(esk4_2(X37,X38),esk5_2(X37,X38))|v13_waybel_0(X38,k3_yellow_1(X37))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37)))))&(r1_tarski(esk5_2(X37,X38),X37)|v13_waybel_0(X38,k3_yellow_1(X37))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37))))))&(r2_hidden(esk4_2(X37,X38),X38)|v13_waybel_0(X38,k3_yellow_1(X37))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37))))))&(~r2_hidden(esk5_2(X37,X38),X38)|v13_waybel_0(X38,k3_yellow_1(X37))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X37))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).
% 0.50/0.66  fof(c_0_42, plain, ![X23]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X23)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.50/0.66  cnf(c_0_43, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.50/0.66  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.50/0.66  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.50/0.66  cnf(c_0_46, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_38])).
% 0.50/0.66  cnf(c_0_47, plain, (m1_subset_1(X1,X2)|~r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.50/0.66  cnf(c_0_48, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.66  cnf(c_0_49, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,k3_yellow_1(X2))|~r1_tarski(X3,X4)|~r1_tarski(X4,X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.50/0.66  cnf(c_0_50, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.50/0.66  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.50/0.66  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.50/0.66  fof(c_0_53, plain, ![X11, X12]:((~r2_hidden(esk2_2(X11,X12),X11)|~r2_hidden(esk2_2(X11,X12),X12)|X11=X12)&(r2_hidden(esk2_2(X11,X12),X11)|r2_hidden(esk2_2(X11,X12),X12)|X11=X12)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.50/0.66  cnf(c_0_54, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(k1_zfmisc_1(X3),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_33, c_0_47])).
% 0.50/0.66  cnf(c_0_55, plain, (r1_tarski(X1,X2)|k1_zfmisc_1(X1)!=k1_zfmisc_1(X2)), inference(spm,[status(thm)],[c_0_48, c_0_40])).
% 0.50/0.66  cnf(c_0_56, plain, (r2_hidden(X4,X1)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)|~r2_hidden(X3,X1)|~v13_waybel_0(X1,k2_yellow_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_24]), c_0_24])).
% 0.50/0.66  cnf(c_0_57, negated_conjecture, (v13_waybel_0(esk7_0,k3_yellow_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.66  cnf(c_0_58, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.50/0.66  cnf(c_0_59, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_50])).
% 0.50/0.66  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_51, c_0_29])).
% 0.50/0.66  cnf(c_0_61, negated_conjecture, (v1_xboole_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.66  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,X2)|X2!=k1_zfmisc_1(esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_52])).
% 0.50/0.66  cnf(c_0_63, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.50/0.66  cnf(c_0_64, plain, (m1_subset_1(X1,X2)|k1_zfmisc_1(k1_zfmisc_1(X3))!=k1_zfmisc_1(k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.50/0.66  cnf(c_0_65, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,k2_yellow_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~r2_hidden(X4,X2)|~r1_tarski(X1,X3)|~r1_tarski(X4,X1)), inference(rw,[status(thm)],[c_0_56, c_0_32])).
% 0.50/0.66  cnf(c_0_66, negated_conjecture, (v13_waybel_0(esk7_0,k2_yellow_1(k1_zfmisc_1(esk6_0)))), inference(rw,[status(thm)],[c_0_57, c_0_24])).
% 0.50/0.66  cnf(c_0_67, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_29])).
% 0.50/0.66  cnf(c_0_68, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.50/0.66  cnf(c_0_69, negated_conjecture, (r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.50/0.66  cnf(c_0_70, negated_conjecture, (esk7_0=X1|r2_hidden(esk2_2(esk7_0,X1),X1)|r2_hidden(esk2_2(esk7_0,X1),X2)|X2!=k1_zfmisc_1(esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.50/0.66  cnf(c_0_71, plain, (m1_subset_1(X1,X2)|k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X1)))!=k1_zfmisc_1(k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_64, c_0_40])).
% 0.50/0.66  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk7_0)|~r1_tarski(X1,esk6_0)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_38])])).
% 0.50/0.66  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_45, c_0_67])).
% 0.50/0.66  cnf(c_0_74, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.66  cnf(c_0_75, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.50/0.66  cnf(c_0_76, negated_conjecture, (esk7_0=X1|r2_hidden(esk2_2(esk7_0,X1),k1_zfmisc_1(esk6_0))|r2_hidden(esk2_2(esk7_0,X1),X1)), inference(er,[status(thm)],[c_0_70])).
% 0.50/0.66  fof(c_0_77, plain, ![X35, X36]:((~v1_subset_1(X36,X35)|X36!=X35|~m1_subset_1(X36,k1_zfmisc_1(X35)))&(X36=X35|v1_subset_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.50/0.66  cnf(c_0_78, plain, (m1_subset_1(X1,X2)|k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X3)))!=k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_33, c_0_71])).
% 0.50/0.66  cnf(c_0_79, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k3_yellow_1(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.50/0.66  cnf(c_0_80, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k1_zfmisc_1(esk6_0))|~r2_hidden(X2,esk7_0)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.50/0.66  cnf(c_0_81, negated_conjecture, (r2_hidden(k1_xboole_0,esk7_0)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.50/0.66  cnf(c_0_82, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.50/0.66  cnf(c_0_83, negated_conjecture, (k1_zfmisc_1(esk6_0)=esk7_0|r2_hidden(esk2_2(esk7_0,k1_zfmisc_1(esk6_0)),k1_zfmisc_1(esk6_0))), inference(ef,[status(thm)],[c_0_76])).
% 0.50/0.66  cnf(c_0_84, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.50/0.66  cnf(c_0_85, plain, (m1_subset_1(X1,X2)|k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X1))))!=k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_78, c_0_40])).
% 0.50/0.66  cnf(c_0_86, negated_conjecture, (v1_subset_1(esk7_0,u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk6_0))))), inference(rw,[status(thm)],[c_0_79, c_0_24])).
% 0.50/0.66  cnf(c_0_87, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,k1_zfmisc_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_59]), c_0_81])])).
% 0.50/0.66  cnf(c_0_88, negated_conjecture, (k1_zfmisc_1(esk6_0)=esk7_0|~r2_hidden(esk2_2(esk7_0,k1_zfmisc_1(esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.50/0.66  cnf(c_0_89, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_84])).
% 0.50/0.66  cnf(c_0_90, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_85])).
% 0.50/0.66  cnf(c_0_91, negated_conjecture, (v1_subset_1(esk7_0,k1_zfmisc_1(esk6_0))), inference(rw,[status(thm)],[c_0_86, c_0_32])).
% 0.50/0.66  cnf(c_0_92, negated_conjecture, (k1_zfmisc_1(esk6_0)=esk7_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_83]), c_0_88])).
% 0.50/0.66  cnf(c_0_93, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 0.50/0.66  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92]), c_0_93]), ['proof']).
% 0.50/0.66  # SZS output end CNFRefutation
% 0.50/0.66  # Proof object total steps             : 95
% 0.50/0.66  # Proof object clause steps            : 66
% 0.50/0.66  # Proof object formula steps           : 29
% 0.50/0.66  # Proof object conjectures             : 28
% 0.50/0.66  # Proof object clause conjectures      : 25
% 0.50/0.66  # Proof object formula conjectures     : 3
% 0.50/0.66  # Proof object initial clauses used    : 22
% 0.50/0.66  # Proof object initial formulas used   : 14
% 0.50/0.66  # Proof object generating inferences   : 31
% 0.50/0.66  # Proof object simplifying inferences  : 21
% 0.50/0.66  # Training examples: 0 positive, 0 negative
% 0.50/0.66  # Parsed axioms                        : 14
% 0.50/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.66  # Initial clauses                      : 36
% 0.50/0.66  # Removed in clause preprocessing      : 3
% 0.50/0.66  # Initial clauses in saturation        : 33
% 0.50/0.66  # Processed clauses                    : 1279
% 0.50/0.66  # ...of these trivial                  : 12
% 0.50/0.66  # ...subsumed                          : 544
% 0.50/0.66  # ...remaining for further processing  : 723
% 0.50/0.66  # Other redundant clauses eliminated   : 3
% 0.50/0.66  # Clauses deleted for lack of memory   : 0
% 0.50/0.66  # Backward-subsumed                    : 51
% 0.50/0.66  # Backward-rewritten                   : 237
% 0.50/0.66  # Generated clauses                    : 8369
% 0.50/0.66  # ...of the previous two non-trivial   : 8259
% 0.50/0.66  # Contextual simplify-reflections      : 14
% 0.50/0.66  # Paramodulations                      : 8278
% 0.50/0.66  # Factorizations                       : 15
% 0.50/0.66  # Equation resolutions                 : 76
% 0.50/0.66  # Propositional unsat checks           : 0
% 0.50/0.66  #    Propositional check models        : 0
% 0.50/0.66  #    Propositional check unsatisfiable : 0
% 0.50/0.66  #    Propositional clauses             : 0
% 0.50/0.66  #    Propositional clauses after purity: 0
% 0.50/0.66  #    Propositional unsat core size     : 0
% 0.50/0.66  #    Propositional preprocessing time  : 0.000
% 0.50/0.66  #    Propositional encoding time       : 0.000
% 0.50/0.66  #    Propositional solver time         : 0.000
% 0.50/0.66  #    Success case prop preproc time    : 0.000
% 0.50/0.66  #    Success case prop encoding time   : 0.000
% 0.50/0.66  #    Success case prop solver time     : 0.000
% 0.50/0.66  # Current number of processed clauses  : 432
% 0.50/0.66  #    Positive orientable unit clauses  : 12
% 0.50/0.66  #    Positive unorientable unit clauses: 0
% 0.50/0.66  #    Negative unit clauses             : 11
% 0.50/0.66  #    Non-unit-clauses                  : 409
% 0.50/0.66  # Current number of unprocessed clauses: 6751
% 0.50/0.66  # ...number of literals in the above   : 33690
% 0.50/0.66  # Current number of archived formulas  : 0
% 0.50/0.66  # Current number of archived clauses   : 291
% 0.50/0.66  # Clause-clause subsumption calls (NU) : 32317
% 0.50/0.66  # Rec. Clause-clause subsumption calls : 16487
% 0.50/0.66  # Non-unit clause-clause subsumptions  : 342
% 0.50/0.66  # Unit Clause-clause subsumption calls : 1108
% 0.50/0.66  # Rewrite failures with RHS unbound    : 0
% 0.50/0.66  # BW rewrite match attempts            : 29
% 0.50/0.66  # BW rewrite match successes           : 6
% 0.50/0.66  # Condensation attempts                : 0
% 0.50/0.66  # Condensation successes               : 0
% 0.50/0.66  # Termbank termtop insertions          : 136075
% 0.50/0.67  
% 0.50/0.67  # -------------------------------------------------
% 0.50/0.67  # User time                : 0.293 s
% 0.50/0.67  # System time              : 0.017 s
% 0.50/0.67  # Total time               : 0.310 s
% 0.50/0.67  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

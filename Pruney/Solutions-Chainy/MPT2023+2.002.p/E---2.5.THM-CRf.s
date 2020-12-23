%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:38 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 434 expanded)
%              Number of clauses        :   49 ( 150 expanded)
%              Number of leaves         :   11 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  272 (2476 expanded)
%              Number of equality atoms :   22 (  70 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_waybel_9,conjecture,(
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
                 => m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

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

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(fc6_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v3_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v3_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k3_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

fof(c_0_11,negated_conjecture,(
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
                   => m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_waybel_9])).

fof(c_0_12,plain,(
    ! [X36,X37,X38] :
      ( ( m1_subset_1(esk3_3(X36,X37,X38),k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_subset_1(X38,u1_struct_0(k9_yellow_6(X36,X37)))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( esk3_3(X36,X37,X38) = X38
        | ~ m1_subset_1(X38,u1_struct_0(k9_yellow_6(X36,X37)))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( r2_hidden(X37,esk3_3(X36,X37,X38))
        | ~ m1_subset_1(X38,u1_struct_0(k9_yellow_6(X36,X37)))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( v3_pre_topc(esk3_3(X36,X37,X38),X36)
        | ~ m1_subset_1(X38,u1_struct_0(k9_yellow_6(X36,X37)))
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    & m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    & ~ m1_subset_1(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_14,plain,
    ( esk3_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,X1) = X1
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,esk3_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_28,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(k3_xboole_0(X18,X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,esk6_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_3(esk4_0,esk5_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( esk3_3(esk4_0,esk5_0,esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_26])).

fof(c_0_35,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_36,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(X41,X42)
        | ~ r2_hidden(X42,u1_struct_0(k9_yellow_6(X40,X41)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v3_pre_topc(X42,X40)
        | ~ r2_hidden(X42,u1_struct_0(k9_yellow_6(X40,X41)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ r2_hidden(X41,X42)
        | ~ v3_pre_topc(X42,X40)
        | r2_hidden(X42,u1_struct_0(k9_yellow_6(X40,X41)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).

fof(c_0_37,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | m1_subset_1(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(k3_xboole_0(X3,X4),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_34])).

fof(c_0_44,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(k3_xboole_0(esk7_0,X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_30])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(k3_xboole_0(esk6_0,esk7_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_53])).

cnf(c_0_58,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k3_xboole_0(esk6_0,X1),u1_struct_0(k9_yellow_6(esk4_0,X2)))
    | ~ v3_pre_topc(k3_xboole_0(esk6_0,X1),esk4_0)
    | ~ r2_hidden(X2,k3_xboole_0(esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,k3_xboole_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_61,plain,(
    ! [X33,X34,X35] :
      ( ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ v3_pre_topc(X34,X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ v3_pre_topc(X35,X33)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
      | v3_pre_topc(k3_xboole_0(X34,X35),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).

cnf(c_0_62,negated_conjecture,
    ( v3_pre_topc(esk3_3(esk4_0,esk5_0,X1),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))
    | ~ v3_pre_topc(k3_xboole_0(esk6_0,esk7_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( v3_pre_topc(k3_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_26]),c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_22]),c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_34]),c_0_26])])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),c_0_16]),c_0_17]),c_0_67]),c_0_41])])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.21/0.47  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.028 s
% 0.21/0.47  # Presaturation interreduction done
% 0.21/0.47  
% 0.21/0.47  # Proof found!
% 0.21/0.47  # SZS status Theorem
% 0.21/0.47  # SZS output start CNFRefutation
% 0.21/0.47  fof(t22_waybel_9, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_9)).
% 0.21/0.47  fof(t38_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&X4=X3)&r2_hidden(X2,X4))&v3_pre_topc(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 0.21/0.47  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.21/0.47  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.21/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.47  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.21/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.47  fof(t39_yellow_6, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))<=>(r2_hidden(X2,X3)&v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 0.21/0.47  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.47  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.47  fof(fc6_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v3_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v3_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k3_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_tops_1)).
% 0.21/0.47  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))=>![X4]:(m1_subset_1(X4,u1_struct_0(k9_yellow_6(X1,X2)))=>m1_subset_1(k3_xboole_0(X3,X4),u1_struct_0(k9_yellow_6(X1,X2)))))))), inference(assume_negation,[status(cth)],[t22_waybel_9])).
% 0.21/0.47  fof(c_0_12, plain, ![X36, X37, X38]:((((m1_subset_1(esk3_3(X36,X37,X38),k1_zfmisc_1(u1_struct_0(X36)))|~m1_subset_1(X38,u1_struct_0(k9_yellow_6(X36,X37)))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(esk3_3(X36,X37,X38)=X38|~m1_subset_1(X38,u1_struct_0(k9_yellow_6(X36,X37)))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))&(r2_hidden(X37,esk3_3(X36,X37,X38))|~m1_subset_1(X38,u1_struct_0(k9_yellow_6(X36,X37)))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))))&(v3_pre_topc(esk3_3(X36,X37,X38),X36)|~m1_subset_1(X38,u1_struct_0(k9_yellow_6(X36,X37)))|~m1_subset_1(X37,u1_struct_0(X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).
% 0.21/0.47  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))&(m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))&~m1_subset_1(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.21/0.47  cnf(c_0_14, plain, (esk3_3(X1,X2,X3)=X3|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.47  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.47  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.47  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.47  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.47  fof(c_0_19, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.21/0.47  cnf(c_0_20, plain, (m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.47  cnf(c_0_21, negated_conjecture, (esk3_3(esk4_0,esk5_0,X1)=X1|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.21/0.47  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.47  fof(c_0_23, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.21/0.47  cnf(c_0_24, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.47  cnf(c_0_25, plain, (r2_hidden(X1,esk3_3(X2,X1,X3))|v2_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.47  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.47  fof(c_0_27, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.47  fof(c_0_28, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|r1_tarski(k3_xboole_0(X18,X20),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.21/0.47  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.21/0.47  cnf(c_0_30, negated_conjecture, (esk3_3(esk4_0,esk5_0,esk6_0)=esk6_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.47  cnf(c_0_31, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.47  cnf(c_0_32, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 0.21/0.47  cnf(c_0_33, negated_conjecture, (r2_hidden(esk5_0,esk3_3(esk4_0,esk5_0,X1))|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.21/0.47  cnf(c_0_34, negated_conjecture, (esk3_3(esk4_0,esk5_0,esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_21, c_0_26])).
% 0.21/0.47  fof(c_0_35, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.47  fof(c_0_36, plain, ![X40, X41, X42]:(((r2_hidden(X41,X42)|~r2_hidden(X42,u1_struct_0(k9_yellow_6(X40,X41)))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))&(v3_pre_topc(X42,X40)|~r2_hidden(X42,u1_struct_0(k9_yellow_6(X40,X41)))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))))&(~r2_hidden(X41,X42)|~v3_pre_topc(X42,X40)|r2_hidden(X42,u1_struct_0(k9_yellow_6(X40,X41)))|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X40)))|~m1_subset_1(X41,u1_struct_0(X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_6])])])])])).
% 0.21/0.47  fof(c_0_37, plain, ![X30, X31, X32]:(~r2_hidden(X30,X31)|~m1_subset_1(X31,k1_zfmisc_1(X32))|m1_subset_1(X30,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.47  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.47  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.47  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.47  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_22])])).
% 0.21/0.47  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~m1_subset_1(k3_xboole_0(X3,X4),k1_zfmisc_1(X2))|~r2_hidden(X1,X4)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.47  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_34])).
% 0.21/0.47  fof(c_0_44, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.47  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.47  cnf(c_0_46, plain, (r2_hidden(X2,u1_struct_0(k9_yellow_6(X3,X1)))|v2_struct_0(X3)|~r2_hidden(X1,X2)|~v3_pre_topc(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.47  cnf(c_0_47, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.47  cnf(c_0_48, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.47  cnf(c_0_49, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.47  cnf(c_0_50, negated_conjecture, (r2_hidden(esk5_0,X1)|~m1_subset_1(k3_xboole_0(esk7_0,X2),k1_zfmisc_1(X1))|~r2_hidden(esk5_0,X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.47  cnf(c_0_51, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_30])).
% 0.21/0.47  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.47  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.21/0.47  cnf(c_0_54, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X3)))|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.47  cnf(c_0_55, negated_conjecture, (m1_subset_1(k3_xboole_0(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.47  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_0,X1)|~m1_subset_1(k3_xboole_0(esk6_0,esk7_0),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.21/0.47  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_53])).
% 0.21/0.47  cnf(c_0_58, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.47  cnf(c_0_59, negated_conjecture, (r2_hidden(k3_xboole_0(esk6_0,X1),u1_struct_0(k9_yellow_6(esk4_0,X2)))|~v3_pre_topc(k3_xboole_0(esk6_0,X1),esk4_0)|~r2_hidden(X2,k3_xboole_0(esk6_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_16]), c_0_17])]), c_0_18])).
% 0.21/0.47  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,k3_xboole_0(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.47  fof(c_0_61, plain, ![X33, X34, X35]:(~v2_pre_topc(X33)|~l1_pre_topc(X33)|~v3_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~v3_pre_topc(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|v3_pre_topc(k3_xboole_0(X34,X35),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_tops_1])])).
% 0.21/0.47  cnf(c_0_62, negated_conjecture, (v3_pre_topc(esk3_3(esk4_0,esk5_0,X1),esk4_0)|~m1_subset_1(X1,u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.21/0.47  cnf(c_0_63, negated_conjecture, (r2_hidden(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))|~v3_pre_topc(k3_xboole_0(esk6_0,esk7_0),esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.21/0.47  cnf(c_0_64, plain, (v3_pre_topc(k3_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.47  cnf(c_0_65, negated_conjecture, (v3_pre_topc(esk7_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_26]), c_0_34])).
% 0.21/0.47  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_22]), c_0_30])).
% 0.21/0.47  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_34]), c_0_26])])).
% 0.21/0.47  cnf(c_0_68, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_57])).
% 0.21/0.47  cnf(c_0_69, negated_conjecture, (r2_hidden(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66]), c_0_16]), c_0_17]), c_0_67]), c_0_41])])).
% 0.21/0.47  cnf(c_0_70, negated_conjecture, (~m1_subset_1(k3_xboole_0(esk6_0,esk7_0),u1_struct_0(k9_yellow_6(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.47  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), ['proof']).
% 0.21/0.47  # SZS output end CNFRefutation
% 0.21/0.47  # Proof object total steps             : 72
% 0.21/0.47  # Proof object clause steps            : 49
% 0.21/0.47  # Proof object formula steps           : 23
% 0.21/0.47  # Proof object conjectures             : 31
% 0.21/0.47  # Proof object clause conjectures      : 28
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 21
% 0.21/0.47  # Proof object initial formulas used   : 11
% 0.21/0.47  # Proof object generating inferences   : 25
% 0.21/0.47  # Proof object simplifying inferences  : 40
% 0.21/0.47  # Training examples: 0 positive, 0 negative
% 0.21/0.47  # Parsed axioms                        : 12
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 33
% 0.21/0.47  # Removed in clause preprocessing      : 0
% 0.21/0.47  # Initial clauses in saturation        : 33
% 0.21/0.47  # Processed clauses                    : 1080
% 0.21/0.47  # ...of these trivial                  : 101
% 0.21/0.47  # ...subsumed                          : 383
% 0.21/0.47  # ...remaining for further processing  : 596
% 0.21/0.47  # Other redundant clauses eliminated   : 5
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 0
% 0.21/0.47  # Backward-rewritten                   : 18
% 0.21/0.47  # Generated clauses                    : 4702
% 0.21/0.47  # ...of the previous two non-trivial   : 3405
% 0.21/0.47  # Contextual simplify-reflections      : 2
% 0.21/0.47  # Paramodulations                      : 4685
% 0.21/0.47  # Factorizations                       : 12
% 0.21/0.47  # Equation resolutions                 : 5
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.47  # Current number of processed clauses  : 541
% 0.21/0.47  #    Positive orientable unit clauses  : 247
% 0.21/0.47  #    Positive unorientable unit clauses: 1
% 0.21/0.47  #    Negative unit clauses             : 2
% 0.21/0.47  #    Non-unit-clauses                  : 291
% 0.21/0.47  # Current number of unprocessed clauses: 2363
% 0.21/0.47  # ...number of literals in the above   : 7595
% 0.21/0.47  # Current number of archived formulas  : 0
% 0.21/0.47  # Current number of archived clauses   : 50
% 0.21/0.47  # Clause-clause subsumption calls (NU) : 10839
% 0.21/0.47  # Rec. Clause-clause subsumption calls : 8612
% 0.21/0.47  # Non-unit clause-clause subsumptions  : 385
% 0.21/0.47  # Unit Clause-clause subsumption calls : 806
% 0.21/0.47  # Rewrite failures with RHS unbound    : 0
% 0.21/0.47  # BW rewrite match attempts            : 5899
% 0.21/0.47  # BW rewrite match successes           : 12
% 0.21/0.47  # Condensation attempts                : 0
% 0.21/0.47  # Condensation successes               : 0
% 0.21/0.47  # Termbank termtop insertions          : 77771
% 0.21/0.48  
% 0.21/0.48  # -------------------------------------------------
% 0.21/0.48  # User time                : 0.124 s
% 0.21/0.48  # System time              : 0.008 s
% 0.21/0.48  # Total time               : 0.132 s
% 0.21/0.48  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

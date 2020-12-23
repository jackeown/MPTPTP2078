%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:57 EST 2020

% Result     : Theorem 1.05s
% Output     : CNFRefutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   54 (  85 expanded)
%              Number of clauses        :   31 (  37 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  254 ( 465 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_11,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | r1_tarski(k3_tarski(X28),k3_tarski(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X30] : k3_tarski(k1_zfmisc_1(X30)) = X30 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,plain,(
    ! [X40] :
      ( ~ l1_pre_topc(X40)
      | m1_subset_1(u1_pre_topc(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k3_tarski(X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

fof(c_0_25,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( r2_hidden(X19,esk3_3(X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | X18 != k3_tarski(X17) )
      & ( r2_hidden(esk3_3(X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k3_tarski(X17) )
      & ( ~ r2_hidden(X21,X22)
        | ~ r2_hidden(X22,X17)
        | r2_hidden(X21,X18)
        | X18 != k3_tarski(X17) )
      & ( ~ r2_hidden(esk4_2(X23,X24),X24)
        | ~ r2_hidden(esk4_2(X23,X24),X26)
        | ~ r2_hidden(X26,X23)
        | X24 = k3_tarski(X23) )
      & ( r2_hidden(esk4_2(X23,X24),esk5_2(X23,X24))
        | r2_hidden(esk4_2(X23,X24),X24)
        | X24 = k3_tarski(X23) )
      & ( r2_hidden(esk5_2(X23,X24),X23)
        | r2_hidden(esk4_2(X23,X24),X24)
        | X24 = k3_tarski(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,k3_tarski(u1_pre_topc(X2))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v2_pre_topc(esk9_0)
    & l1_pre_topc(esk9_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0))) != u1_struct_0(esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36] :
      ( ( r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))
        | ~ r1_tarski(X34,u1_pre_topc(X33))
        | r2_hidden(k5_setfam_1(u1_struct_0(X33),X34),u1_pre_topc(X33))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ r2_hidden(X35,u1_pre_topc(X33))
        | ~ r2_hidden(X36,u1_pre_topc(X33))
        | r2_hidden(k9_subset_1(u1_struct_0(X33),X35,X36),u1_pre_topc(X33))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk7_1(X33),k1_zfmisc_1(u1_struct_0(X33)))
        | m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk8_1(X33),k1_zfmisc_1(u1_struct_0(X33)))
        | m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(esk7_1(X33),u1_pre_topc(X33))
        | m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(esk8_1(X33),u1_pre_topc(X33))
        | m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X33),esk7_1(X33),esk8_1(X33)),u1_pre_topc(X33))
        | m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk7_1(X33),k1_zfmisc_1(u1_struct_0(X33)))
        | r1_tarski(esk6_1(X33),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk8_1(X33),k1_zfmisc_1(u1_struct_0(X33)))
        | r1_tarski(esk6_1(X33),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(esk7_1(X33),u1_pre_topc(X33))
        | r1_tarski(esk6_1(X33),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(esk8_1(X33),u1_pre_topc(X33))
        | r1_tarski(esk6_1(X33),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X33),esk7_1(X33),esk8_1(X33)),u1_pre_topc(X33))
        | r1_tarski(esk6_1(X33),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk7_1(X33),k1_zfmisc_1(u1_struct_0(X33)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk8_1(X33),k1_zfmisc_1(u1_struct_0(X33)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(esk7_1(X33),u1_pre_topc(X33))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(esk8_1(X33),u1_pre_topc(X33))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X33),esk7_1(X33),esk8_1(X33)),u1_pre_topc(X33))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))
        | ~ r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))
        | v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(X1)),X2)
    | r2_hidden(esk2_2(k3_tarski(u1_pre_topc(X1)),X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k3_tarski(u1_pre_topc(esk9_0)),X1)
    | r2_hidden(esk2_2(k3_tarski(u1_pre_topc(esk9_0)),X1),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k3_tarski(u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,plain,(
    ! [X41] :
      ( v1_xboole_0(X41)
      | ~ r2_hidden(k3_tarski(X41),X41)
      | k4_yellow_0(k2_yellow_1(X41)) = k3_tarski(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_40,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k3_tarski(u1_pre_topc(esk9_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k3_tarski(u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk2_2(X1,k3_tarski(u1_pre_topc(X2))),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk9_0)) = u1_struct_0(esk9_0)
    | ~ r1_tarski(u1_struct_0(esk9_0),k3_tarski(u1_pre_topc(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(u1_struct_0(X1),k3_tarski(u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_49,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk9_0)) = u1_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_32])])).

cnf(c_0_51,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0))) != u1_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_34]),c_0_48]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.05/1.21  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.05/1.21  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.05/1.21  #
% 1.05/1.21  # Preprocessing time       : 0.029 s
% 1.05/1.21  # Presaturation interreduction done
% 1.05/1.21  
% 1.05/1.21  # Proof found!
% 1.05/1.21  # SZS status Theorem
% 1.05/1.21  # SZS output start CNFRefutation
% 1.05/1.21  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.05/1.21  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.05/1.21  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.05/1.21  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.05/1.21  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 1.05/1.21  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 1.05/1.21  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 1.05/1.21  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 1.05/1.21  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.05/1.21  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 1.05/1.21  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.05/1.21  fof(c_0_11, plain, ![X28, X29]:(~r1_tarski(X28,X29)|r1_tarski(k3_tarski(X28),k3_tarski(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 1.05/1.21  fof(c_0_12, plain, ![X30]:k3_tarski(k1_zfmisc_1(X30))=X30, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 1.05/1.21  fof(c_0_13, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.05/1.21  cnf(c_0_14, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.05/1.21  cnf(c_0_15, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.05/1.21  fof(c_0_16, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.05/1.21  fof(c_0_17, plain, ![X40]:(~l1_pre_topc(X40)|m1_subset_1(u1_pre_topc(X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X40))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 1.05/1.21  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.05/1.21  cnf(c_0_19, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.05/1.21  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.05/1.21  cnf(c_0_21, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.05/1.21  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,k3_tarski(X3))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.05/1.21  cnf(c_0_23, plain, (r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.05/1.21  fof(c_0_24, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 1.05/1.21  fof(c_0_25, plain, ![X17, X18, X19, X21, X22, X23, X24, X26]:((((r2_hidden(X19,esk3_3(X17,X18,X19))|~r2_hidden(X19,X18)|X18!=k3_tarski(X17))&(r2_hidden(esk3_3(X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k3_tarski(X17)))&(~r2_hidden(X21,X22)|~r2_hidden(X22,X17)|r2_hidden(X21,X18)|X18!=k3_tarski(X17)))&((~r2_hidden(esk4_2(X23,X24),X24)|(~r2_hidden(esk4_2(X23,X24),X26)|~r2_hidden(X26,X23))|X24=k3_tarski(X23))&((r2_hidden(esk4_2(X23,X24),esk5_2(X23,X24))|r2_hidden(esk4_2(X23,X24),X24)|X24=k3_tarski(X23))&(r2_hidden(esk5_2(X23,X24),X23)|r2_hidden(esk4_2(X23,X24),X24)|X24=k3_tarski(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 1.05/1.21  cnf(c_0_26, plain, (r2_hidden(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~r2_hidden(X1,k3_tarski(u1_pre_topc(X2)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.05/1.21  cnf(c_0_27, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.05/1.21  fof(c_0_28, negated_conjecture, (((~v2_struct_0(esk9_0)&v2_pre_topc(esk9_0))&l1_pre_topc(esk9_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0)))!=u1_struct_0(esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 1.05/1.21  cnf(c_0_29, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.05/1.21  fof(c_0_30, plain, ![X33, X34, X35, X36]:((((r2_hidden(u1_struct_0(X33),u1_pre_topc(X33))|~v2_pre_topc(X33)|~l1_pre_topc(X33))&(~m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))|(~r1_tarski(X34,u1_pre_topc(X33))|r2_hidden(k5_setfam_1(u1_struct_0(X33),X34),u1_pre_topc(X33)))|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X33)))|(~r2_hidden(X35,u1_pre_topc(X33))|~r2_hidden(X36,u1_pre_topc(X33))|r2_hidden(k9_subset_1(u1_struct_0(X33),X35,X36),u1_pre_topc(X33))))|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(((m1_subset_1(esk7_1(X33),k1_zfmisc_1(u1_struct_0(X33)))|(m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&((m1_subset_1(esk8_1(X33),k1_zfmisc_1(u1_struct_0(X33)))|(m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&(((r2_hidden(esk7_1(X33),u1_pre_topc(X33))|(m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&(r2_hidden(esk8_1(X33),u1_pre_topc(X33))|(m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~r2_hidden(k9_subset_1(u1_struct_0(X33),esk7_1(X33),esk8_1(X33)),u1_pre_topc(X33))|(m1_subset_1(esk6_1(X33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33)))))&(((m1_subset_1(esk7_1(X33),k1_zfmisc_1(u1_struct_0(X33)))|(r1_tarski(esk6_1(X33),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&((m1_subset_1(esk8_1(X33),k1_zfmisc_1(u1_struct_0(X33)))|(r1_tarski(esk6_1(X33),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&(((r2_hidden(esk7_1(X33),u1_pre_topc(X33))|(r1_tarski(esk6_1(X33),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&(r2_hidden(esk8_1(X33),u1_pre_topc(X33))|(r1_tarski(esk6_1(X33),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~r2_hidden(k9_subset_1(u1_struct_0(X33),esk7_1(X33),esk8_1(X33)),u1_pre_topc(X33))|(r1_tarski(esk6_1(X33),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33)))))&((m1_subset_1(esk7_1(X33),k1_zfmisc_1(u1_struct_0(X33)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&((m1_subset_1(esk8_1(X33),k1_zfmisc_1(u1_struct_0(X33)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&(((r2_hidden(esk7_1(X33),u1_pre_topc(X33))|(~r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33))&(r2_hidden(esk8_1(X33),u1_pre_topc(X33))|(~r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~r2_hidden(k9_subset_1(u1_struct_0(X33),esk7_1(X33),esk8_1(X33)),u1_pre_topc(X33))|(~r2_hidden(k5_setfam_1(u1_struct_0(X33),esk6_1(X33)),u1_pre_topc(X33))|~r2_hidden(u1_struct_0(X33),u1_pre_topc(X33)))|v2_pre_topc(X33)|~l1_pre_topc(X33)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 1.05/1.21  cnf(c_0_31, plain, (r1_tarski(k3_tarski(u1_pre_topc(X1)),X2)|r2_hidden(esk2_2(k3_tarski(u1_pre_topc(X1)),X2),u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.05/1.21  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.05/1.21  cnf(c_0_33, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_29])).
% 1.05/1.21  cnf(c_0_34, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.05/1.21  fof(c_0_35, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.05/1.21  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.05/1.21  cnf(c_0_37, negated_conjecture, (r1_tarski(k3_tarski(u1_pre_topc(esk9_0)),X1)|r2_hidden(esk2_2(k3_tarski(u1_pre_topc(esk9_0)),X1),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.05/1.21  cnf(c_0_38, plain, (r2_hidden(X1,k3_tarski(u1_pre_topc(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.05/1.21  fof(c_0_39, plain, ![X41]:(v1_xboole_0(X41)|(~r2_hidden(k3_tarski(X41),X41)|k4_yellow_0(k2_yellow_1(X41))=k3_tarski(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 1.05/1.21  fof(c_0_40, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.05/1.21  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.05/1.21  cnf(c_0_42, negated_conjecture, (r1_tarski(k3_tarski(u1_pre_topc(esk9_0)),u1_struct_0(esk9_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.05/1.21  cnf(c_0_43, plain, (r1_tarski(X1,k3_tarski(u1_pre_topc(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(esk2_2(X1,k3_tarski(u1_pre_topc(X2))),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_36, c_0_38])).
% 1.05/1.21  cnf(c_0_44, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.05/1.21  cnf(c_0_45, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.05/1.21  cnf(c_0_46, negated_conjecture, (k3_tarski(u1_pre_topc(esk9_0))=u1_struct_0(esk9_0)|~r1_tarski(u1_struct_0(esk9_0),k3_tarski(u1_pre_topc(esk9_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.05/1.21  cnf(c_0_47, plain, (r1_tarski(u1_struct_0(X1),k3_tarski(u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_27])).
% 1.05/1.21  cnf(c_0_48, negated_conjecture, (v2_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.05/1.21  cnf(c_0_49, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_44, c_0_45])).
% 1.05/1.21  cnf(c_0_50, negated_conjecture, (k3_tarski(u1_pre_topc(esk9_0))=u1_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_32])])).
% 1.05/1.21  cnf(c_0_51, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0)))!=u1_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.05/1.21  cnf(c_0_52, negated_conjecture, (~r2_hidden(u1_struct_0(esk9_0),u1_pre_topc(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 1.05/1.21  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_34]), c_0_48]), c_0_32])]), ['proof']).
% 1.05/1.21  # SZS output end CNFRefutation
% 1.05/1.21  # Proof object total steps             : 54
% 1.05/1.21  # Proof object clause steps            : 31
% 1.05/1.21  # Proof object formula steps           : 23
% 1.05/1.21  # Proof object conjectures             : 12
% 1.05/1.21  # Proof object clause conjectures      : 9
% 1.05/1.21  # Proof object formula conjectures     : 3
% 1.05/1.21  # Proof object initial clauses used    : 15
% 1.05/1.21  # Proof object initial formulas used   : 11
% 1.05/1.21  # Proof object generating inferences   : 14
% 1.05/1.21  # Proof object simplifying inferences  : 9
% 1.05/1.21  # Training examples: 0 positive, 0 negative
% 1.05/1.21  # Parsed axioms                        : 11
% 1.05/1.21  # Removed by relevancy pruning/SinE    : 0
% 1.05/1.21  # Initial clauses                      : 42
% 1.05/1.21  # Removed in clause preprocessing      : 0
% 1.05/1.21  # Initial clauses in saturation        : 42
% 1.05/1.21  # Processed clauses                    : 7584
% 1.05/1.21  # ...of these trivial                  : 0
% 1.05/1.21  # ...subsumed                          : 6632
% 1.05/1.21  # ...remaining for further processing  : 952
% 1.05/1.21  # Other redundant clauses eliminated   : 5
% 1.05/1.21  # Clauses deleted for lack of memory   : 0
% 1.05/1.21  # Backward-subsumed                    : 20
% 1.05/1.21  # Backward-rewritten                   : 141
% 1.05/1.21  # Generated clauses                    : 108714
% 1.05/1.21  # ...of the previous two non-trivial   : 108690
% 1.05/1.21  # Contextual simplify-reflections      : 12
% 1.05/1.21  # Paramodulations                      : 108707
% 1.05/1.21  # Factorizations                       : 2
% 1.05/1.21  # Equation resolutions                 : 5
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
% 1.05/1.21  # Current number of processed clauses  : 745
% 1.05/1.21  #    Positive orientable unit clauses  : 5
% 1.05/1.21  #    Positive unorientable unit clauses: 0
% 1.05/1.21  #    Negative unit clauses             : 3
% 1.05/1.21  #    Non-unit-clauses                  : 737
% 1.05/1.21  # Current number of unprocessed clauses: 101189
% 1.05/1.21  # ...number of literals in the above   : 462447
% 1.05/1.21  # Current number of archived formulas  : 0
% 1.05/1.21  # Current number of archived clauses   : 202
% 1.05/1.21  # Clause-clause subsumption calls (NU) : 215706
% 1.05/1.21  # Rec. Clause-clause subsumption calls : 97963
% 1.05/1.21  # Non-unit clause-clause subsumptions  : 6664
% 1.05/1.21  # Unit Clause-clause subsumption calls : 26
% 1.05/1.21  # Rewrite failures with RHS unbound    : 0
% 1.05/1.21  # BW rewrite match attempts            : 1
% 1.05/1.21  # BW rewrite match successes           : 1
% 1.05/1.21  # Condensation attempts                : 0
% 1.05/1.21  # Condensation successes               : 0
% 1.05/1.21  # Termbank termtop insertions          : 1844942
% 1.05/1.21  
% 1.05/1.21  # -------------------------------------------------
% 1.05/1.21  # User time                : 0.822 s
% 1.05/1.21  # System time              : 0.044 s
% 1.05/1.21  # Total time               : 0.866 s
% 1.05/1.21  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 11:15:59 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 117 expanded)
%              Number of clauses        :   38 (  51 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  271 ( 668 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,plain,(
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | m1_subset_1(u1_pre_topc(X39),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X39)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk8_0)
    & v2_pre_topc(esk8_0)
    & l1_pre_topc(esk8_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0))) != u1_struct_0(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | r1_tarski(k3_tarski(X24),k3_tarski(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(u1_pre_topc(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(u1_pre_topc(X1),X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(X15,esk2_3(X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X18,X13)
        | r2_hidden(X17,X14)
        | X14 != k3_tarski(X13) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_hidden(esk3_2(X19,X20),X22)
        | ~ r2_hidden(X22,X19)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X19)
        | r2_hidden(esk3_2(X19,X20),X20)
        | X20 = k3_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(u1_pre_topc(esk8_0),X1),k1_zfmisc_1(u1_struct_0(esk8_0)))
    | r1_tarski(u1_pre_topc(esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X26] : k3_tarski(k1_zfmisc_1(X26)) = X26 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X32,X33,X34,X35] :
      ( ( r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ r1_tarski(X33,u1_pre_topc(X32))
        | r2_hidden(k5_setfam_1(u1_struct_0(X32),X33),u1_pre_topc(X32))
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ r2_hidden(X34,u1_pre_topc(X32))
        | ~ r2_hidden(X35,u1_pre_topc(X32))
        | r2_hidden(k9_subset_1(u1_struct_0(X32),X34,X35),u1_pre_topc(X32))
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk6_1(X32),k1_zfmisc_1(u1_struct_0(X32)))
        | m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk7_1(X32),k1_zfmisc_1(u1_struct_0(X32)))
        | m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r2_hidden(esk6_1(X32),u1_pre_topc(X32))
        | m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r2_hidden(esk7_1(X32),u1_pre_topc(X32))
        | m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X32),esk6_1(X32),esk7_1(X32)),u1_pre_topc(X32))
        | m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk6_1(X32),k1_zfmisc_1(u1_struct_0(X32)))
        | r1_tarski(esk5_1(X32),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk7_1(X32),k1_zfmisc_1(u1_struct_0(X32)))
        | r1_tarski(esk5_1(X32),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r2_hidden(esk6_1(X32),u1_pre_topc(X32))
        | r1_tarski(esk5_1(X32),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r2_hidden(esk7_1(X32),u1_pre_topc(X32))
        | r1_tarski(esk5_1(X32),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X32),esk6_1(X32),esk7_1(X32)),u1_pre_topc(X32))
        | r1_tarski(esk5_1(X32),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk6_1(X32),k1_zfmisc_1(u1_struct_0(X32)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk7_1(X32),k1_zfmisc_1(u1_struct_0(X32)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r2_hidden(esk6_1(X32),u1_pre_topc(X32))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r2_hidden(esk7_1(X32),u1_pre_topc(X32))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X32),esk6_1(X32),esk7_1(X32)),u1_pre_topc(X32))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))
        | ~ r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))
        | v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(k3_tarski(X1),X2),k3_tarski(X3))
    | r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_38,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(u1_pre_topc(esk8_0)),X1),u1_struct_0(esk8_0))
    | r1_tarski(k3_tarski(u1_pre_topc(esk8_0)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_tarski(u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_tarski(u1_pre_topc(esk8_0)),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k3_tarski(u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk1_2(X1,k3_tarski(u1_pre_topc(X2))),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_40])).

cnf(c_0_46,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X40] :
      ( v1_xboole_0(X40)
      | ~ r2_hidden(k3_tarski(X40),X40)
      | k4_yellow_0(k2_yellow_1(X40)) = k3_tarski(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

cnf(c_0_49,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk8_0)) = u1_struct_0(esk8_0)
    | ~ r1_tarski(u1_struct_0(esk8_0),k3_tarski(u1_pre_topc(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(u1_struct_0(X1),k3_tarski(u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_52,plain,
    ( ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(u1_pre_topc(X1),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk8_0)) = u1_struct_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_24])])).

cnf(c_0_56,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0))) != u1_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,plain,
    ( ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk8_0))
    | ~ r2_hidden(u1_struct_0(esk8_0),u1_pre_topc(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk8_0),u1_pre_topc(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_51]),c_0_24])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_36]),c_0_51]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:31:30 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.52  #
% 0.18/0.52  # Preprocessing time       : 0.027 s
% 0.18/0.52  # Presaturation interreduction done
% 0.18/0.52  
% 0.18/0.52  # Proof found!
% 0.18/0.52  # SZS status Theorem
% 0.18/0.52  # SZS output start CNFRefutation
% 0.18/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.52  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.52  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.18/0.52  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.18/0.52  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.18/0.52  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.18/0.52  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.18/0.52  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.18/0.52  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.18/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.52  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.18/0.52  fof(c_0_11, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.52  fof(c_0_12, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.52  fof(c_0_13, plain, ![X39]:(~l1_pre_topc(X39)|m1_subset_1(u1_pre_topc(X39),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X39))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.18/0.52  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.52  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.52  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.52  cnf(c_0_17, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.52  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.18/0.52  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.52  cnf(c_0_20, plain, (r1_tarski(u1_pre_topc(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.52  fof(c_0_21, negated_conjecture, (((~v2_struct_0(esk8_0)&v2_pre_topc(esk8_0))&l1_pre_topc(esk8_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0)))!=u1_struct_0(esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.18/0.52  fof(c_0_22, plain, ![X24, X25]:(~r1_tarski(X24,X25)|r1_tarski(k3_tarski(X24),k3_tarski(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.18/0.52  cnf(c_0_23, plain, (r2_hidden(esk1_2(u1_pre_topc(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|r1_tarski(u1_pre_topc(X1),X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.52  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.52  fof(c_0_25, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(X15,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k3_tarski(X13))&(r2_hidden(esk2_3(X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k3_tarski(X13)))&(~r2_hidden(X17,X18)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k3_tarski(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|(~r2_hidden(esk3_2(X19,X20),X22)|~r2_hidden(X22,X19))|X20=k3_tarski(X19))&((r2_hidden(esk3_2(X19,X20),esk4_2(X19,X20))|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))&(r2_hidden(esk4_2(X19,X20),X19)|r2_hidden(esk3_2(X19,X20),X20)|X20=k3_tarski(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.18/0.52  cnf(c_0_26, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.52  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.52  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(u1_pre_topc(esk8_0),X1),k1_zfmisc_1(u1_struct_0(esk8_0)))|r1_tarski(u1_pre_topc(esk8_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.52  fof(c_0_29, plain, ![X26]:k3_tarski(k1_zfmisc_1(X26))=X26, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.18/0.52  cnf(c_0_30, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.52  fof(c_0_31, plain, ![X32, X33, X34, X35]:((((r2_hidden(u1_struct_0(X32),u1_pre_topc(X32))|~v2_pre_topc(X32)|~l1_pre_topc(X32))&(~m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))|(~r1_tarski(X33,u1_pre_topc(X32))|r2_hidden(k5_setfam_1(u1_struct_0(X32),X33),u1_pre_topc(X32)))|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X32)))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X32)))|(~r2_hidden(X34,u1_pre_topc(X32))|~r2_hidden(X35,u1_pre_topc(X32))|r2_hidden(k9_subset_1(u1_struct_0(X32),X34,X35),u1_pre_topc(X32))))|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(((m1_subset_1(esk6_1(X32),k1_zfmisc_1(u1_struct_0(X32)))|(m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&((m1_subset_1(esk7_1(X32),k1_zfmisc_1(u1_struct_0(X32)))|(m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&(((r2_hidden(esk6_1(X32),u1_pre_topc(X32))|(m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&(r2_hidden(esk7_1(X32),u1_pre_topc(X32))|(m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~r2_hidden(k9_subset_1(u1_struct_0(X32),esk6_1(X32),esk7_1(X32)),u1_pre_topc(X32))|(m1_subset_1(esk5_1(X32),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32)))))&(((m1_subset_1(esk6_1(X32),k1_zfmisc_1(u1_struct_0(X32)))|(r1_tarski(esk5_1(X32),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&((m1_subset_1(esk7_1(X32),k1_zfmisc_1(u1_struct_0(X32)))|(r1_tarski(esk5_1(X32),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&(((r2_hidden(esk6_1(X32),u1_pre_topc(X32))|(r1_tarski(esk5_1(X32),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&(r2_hidden(esk7_1(X32),u1_pre_topc(X32))|(r1_tarski(esk5_1(X32),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~r2_hidden(k9_subset_1(u1_struct_0(X32),esk6_1(X32),esk7_1(X32)),u1_pre_topc(X32))|(r1_tarski(esk5_1(X32),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32)))))&((m1_subset_1(esk6_1(X32),k1_zfmisc_1(u1_struct_0(X32)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&((m1_subset_1(esk7_1(X32),k1_zfmisc_1(u1_struct_0(X32)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&(((r2_hidden(esk6_1(X32),u1_pre_topc(X32))|(~r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32))&(r2_hidden(esk7_1(X32),u1_pre_topc(X32))|(~r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~r2_hidden(k9_subset_1(u1_struct_0(X32),esk6_1(X32),esk7_1(X32)),u1_pre_topc(X32))|(~r2_hidden(k5_setfam_1(u1_struct_0(X32),esk5_1(X32)),u1_pre_topc(X32))|~r2_hidden(u1_struct_0(X32),u1_pre_topc(X32)))|v2_pre_topc(X32)|~l1_pre_topc(X32)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.18/0.52  cnf(c_0_32, plain, (r2_hidden(esk1_2(k3_tarski(X1),X2),k3_tarski(X3))|r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_19, c_0_26])).
% 0.18/0.52  cnf(c_0_33, negated_conjecture, (r1_tarski(u1_pre_topc(esk8_0),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.52  cnf(c_0_34, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.52  cnf(c_0_35, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_30])).
% 0.18/0.52  cnf(c_0_36, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.52  fof(c_0_37, plain, ![X29, X30, X31]:(~r2_hidden(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(X31))|~v1_xboole_0(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.18/0.52  fof(c_0_38, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.52  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(k3_tarski(u1_pre_topc(esk8_0)),X1),u1_struct_0(esk8_0))|r1_tarski(k3_tarski(u1_pre_topc(esk8_0)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.18/0.52  cnf(c_0_40, plain, (r2_hidden(X1,k3_tarski(u1_pre_topc(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.52  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.52  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.52  cnf(c_0_43, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.52  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_tarski(u1_pre_topc(esk8_0)),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_27, c_0_39])).
% 0.18/0.52  cnf(c_0_45, plain, (r1_tarski(X1,k3_tarski(u1_pre_topc(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(esk1_2(X1,k3_tarski(u1_pre_topc(X2))),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_27, c_0_40])).
% 0.18/0.52  cnf(c_0_46, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.52  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.52  fof(c_0_48, plain, ![X40]:(v1_xboole_0(X40)|(~r2_hidden(k3_tarski(X40),X40)|k4_yellow_0(k2_yellow_1(X40))=k3_tarski(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.18/0.52  cnf(c_0_49, negated_conjecture, (k3_tarski(u1_pre_topc(esk8_0))=u1_struct_0(esk8_0)|~r1_tarski(u1_struct_0(esk8_0),k3_tarski(u1_pre_topc(esk8_0)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.52  cnf(c_0_50, plain, (r1_tarski(u1_struct_0(X1),k3_tarski(u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_15])).
% 0.18/0.52  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.52  cnf(c_0_52, plain, (~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~r1_tarski(u1_pre_topc(X1),X2)), inference(spm,[status(thm)],[c_0_46, c_0_36])).
% 0.18/0.52  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 0.18/0.52  cnf(c_0_54, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.52  cnf(c_0_55, negated_conjecture, (k3_tarski(u1_pre_topc(esk8_0))=u1_struct_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_24])])).
% 0.18/0.52  cnf(c_0_56, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk8_0)))!=u1_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.52  cnf(c_0_57, plain, (~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.52  cnf(c_0_58, negated_conjecture, (v1_xboole_0(u1_pre_topc(esk8_0))|~r2_hidden(u1_struct_0(esk8_0),u1_pre_topc(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.18/0.52  cnf(c_0_59, negated_conjecture, (~r2_hidden(u1_struct_0(esk8_0),u1_pre_topc(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_51]), c_0_24])])).
% 0.18/0.52  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_36]), c_0_51]), c_0_24])]), ['proof']).
% 0.18/0.52  # SZS output end CNFRefutation
% 0.18/0.52  # Proof object total steps             : 61
% 0.18/0.52  # Proof object clause steps            : 38
% 0.18/0.52  # Proof object formula steps           : 23
% 0.18/0.52  # Proof object conjectures             : 15
% 0.18/0.52  # Proof object clause conjectures      : 12
% 0.18/0.52  # Proof object formula conjectures     : 3
% 0.18/0.52  # Proof object initial clauses used    : 17
% 0.18/0.52  # Proof object initial formulas used   : 11
% 0.18/0.52  # Proof object generating inferences   : 19
% 0.18/0.52  # Proof object simplifying inferences  : 13
% 0.18/0.52  # Training examples: 0 positive, 0 negative
% 0.18/0.52  # Parsed axioms                        : 11
% 0.18/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.52  # Initial clauses                      : 41
% 0.18/0.52  # Removed in clause preprocessing      : 0
% 0.18/0.52  # Initial clauses in saturation        : 41
% 0.18/0.52  # Processed clauses                    : 1895
% 0.18/0.52  # ...of these trivial                  : 0
% 0.18/0.52  # ...subsumed                          : 1257
% 0.18/0.52  # ...remaining for further processing  : 638
% 0.18/0.52  # Other redundant clauses eliminated   : 5
% 0.18/0.52  # Clauses deleted for lack of memory   : 0
% 0.18/0.52  # Backward-subsumed                    : 30
% 0.18/0.52  # Backward-rewritten                   : 51
% 0.18/0.52  # Generated clauses                    : 9161
% 0.18/0.52  # ...of the previous two non-trivial   : 9152
% 0.18/0.52  # Contextual simplify-reflections      : 6
% 0.18/0.52  # Paramodulations                      : 9156
% 0.18/0.52  # Factorizations                       : 0
% 0.18/0.52  # Equation resolutions                 : 5
% 0.18/0.52  # Propositional unsat checks           : 0
% 0.18/0.52  #    Propositional check models        : 0
% 0.18/0.52  #    Propositional check unsatisfiable : 0
% 0.18/0.52  #    Propositional clauses             : 0
% 0.18/0.52  #    Propositional clauses after purity: 0
% 0.18/0.52  #    Propositional unsat core size     : 0
% 0.18/0.52  #    Propositional preprocessing time  : 0.000
% 0.18/0.52  #    Propositional encoding time       : 0.000
% 0.18/0.52  #    Propositional solver time         : 0.000
% 0.18/0.52  #    Success case prop preproc time    : 0.000
% 0.18/0.52  #    Success case prop encoding time   : 0.000
% 0.18/0.52  #    Success case prop solver time     : 0.000
% 0.18/0.52  # Current number of processed clauses  : 512
% 0.18/0.52  #    Positive orientable unit clauses  : 8
% 0.18/0.52  #    Positive unorientable unit clauses: 0
% 0.18/0.52  #    Negative unit clauses             : 4
% 0.18/0.52  #    Non-unit-clauses                  : 500
% 0.18/0.52  # Current number of unprocessed clauses: 7331
% 0.18/0.52  # ...number of literals in the above   : 34667
% 0.18/0.52  # Current number of archived formulas  : 0
% 0.18/0.52  # Current number of archived clauses   : 121
% 0.18/0.52  # Clause-clause subsumption calls (NU) : 39347
% 0.18/0.52  # Rec. Clause-clause subsumption calls : 13542
% 0.18/0.52  # Non-unit clause-clause subsumptions  : 1244
% 0.18/0.52  # Unit Clause-clause subsumption calls : 42
% 0.18/0.52  # Rewrite failures with RHS unbound    : 0
% 0.18/0.52  # BW rewrite match attempts            : 3
% 0.18/0.52  # BW rewrite match successes           : 1
% 0.18/0.52  # Condensation attempts                : 0
% 0.18/0.52  # Condensation successes               : 0
% 0.18/0.52  # Termbank termtop insertions          : 150148
% 0.18/0.52  
% 0.18/0.52  # -------------------------------------------------
% 0.18/0.52  # User time                : 0.181 s
% 0.18/0.52  # System time              : 0.015 s
% 0.18/0.52  # Total time               : 0.197 s
% 0.18/0.52  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

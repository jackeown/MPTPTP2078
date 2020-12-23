%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:57 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   54 (  98 expanded)
%              Number of clauses        :   31 (  43 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  267 ( 592 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(X28)))
      | k5_setfam_1(X28,X29) = k3_tarski(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_13,plain,(
    ! [X42] :
      ( ~ l1_pre_topc(X42)
      | m1_subset_1(u1_pre_topc(X42),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X42)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | m1_subset_1(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X35,X36,X37,X38] :
      ( ( r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ m1_subset_1(X36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r1_tarski(X36,u1_pre_topc(X35))
        | r2_hidden(k5_setfam_1(u1_struct_0(X35),X36),u1_pre_topc(X35))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ r2_hidden(X37,u1_pre_topc(X35))
        | ~ r2_hidden(X38,u1_pre_topc(X35))
        | r2_hidden(k9_subset_1(u1_struct_0(X35),X37,X38),u1_pre_topc(X35))
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk7_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk8_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk7_1(X35),u1_pre_topc(X35))
        | m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk8_1(X35),u1_pre_topc(X35))
        | m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X35),esk7_1(X35),esk8_1(X35)),u1_pre_topc(X35))
        | m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk7_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | r1_tarski(esk6_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk8_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | r1_tarski(esk6_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk7_1(X35),u1_pre_topc(X35))
        | r1_tarski(esk6_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk8_1(X35),u1_pre_topc(X35))
        | r1_tarski(esk6_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X35),esk7_1(X35),esk8_1(X35)),u1_pre_topc(X35))
        | r1_tarski(esk6_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk7_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk8_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk7_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( r2_hidden(esk8_1(X35),u1_pre_topc(X35))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X35),esk7_1(X35),esk8_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))
        | ~ r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))
        | v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_18,plain,(
    ! [X43] :
      ( v1_xboole_0(X43)
      | ~ r2_hidden(k3_tarski(X43),X43)
      | k4_yellow_0(k2_yellow_1(X43)) = k3_tarski(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1)) = k3_tarski(u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k3_tarski(u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk9_0)
    & v2_pre_topc(esk9_0)
    & l1_pre_topc(esk9_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0))) != u1_struct_0(esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).

cnf(c_0_39,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(X1)),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_21])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k3_tarski(u1_pre_topc(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk2_2(X1,k3_tarski(u1_pre_topc(X2))),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0))) != u1_struct_0(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = k3_tarski(u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( u1_struct_0(X1) = X2
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),X2)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(u1_struct_0(X1),k3_tarski(u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k3_tarski(u1_pre_topc(esk9_0)) != u1_struct_0(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_52,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.36/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.36/0.55  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.36/0.55  #
% 0.36/0.55  # Preprocessing time       : 0.030 s
% 0.36/0.55  # Presaturation interreduction done
% 0.36/0.55  
% 0.36/0.55  # Proof found!
% 0.36/0.55  # SZS status Theorem
% 0.36/0.55  # SZS output start CNFRefutation
% 0.36/0.55  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.36/0.55  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.36/0.55  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.36/0.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.36/0.55  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.36/0.55  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.36/0.55  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.36/0.55  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.36/0.55  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.36/0.55  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.36/0.55  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.36/0.55  fof(c_0_11, plain, ![X17, X18, X19, X21, X22, X23, X24, X26]:((((r2_hidden(X19,esk3_3(X17,X18,X19))|~r2_hidden(X19,X18)|X18!=k3_tarski(X17))&(r2_hidden(esk3_3(X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k3_tarski(X17)))&(~r2_hidden(X21,X22)|~r2_hidden(X22,X17)|r2_hidden(X21,X18)|X18!=k3_tarski(X17)))&((~r2_hidden(esk4_2(X23,X24),X24)|(~r2_hidden(esk4_2(X23,X24),X26)|~r2_hidden(X26,X23))|X24=k3_tarski(X23))&((r2_hidden(esk4_2(X23,X24),esk5_2(X23,X24))|r2_hidden(esk4_2(X23,X24),X24)|X24=k3_tarski(X23))&(r2_hidden(esk5_2(X23,X24),X23)|r2_hidden(esk4_2(X23,X24),X24)|X24=k3_tarski(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.36/0.55  fof(c_0_12, plain, ![X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(X28)))|k5_setfam_1(X28,X29)=k3_tarski(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.36/0.55  fof(c_0_13, plain, ![X42]:(~l1_pre_topc(X42)|m1_subset_1(u1_pre_topc(X42),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X42))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.36/0.55  fof(c_0_14, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.36/0.55  fof(c_0_15, plain, ![X32, X33, X34]:(~r2_hidden(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(X34))|m1_subset_1(X32,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.36/0.55  cnf(c_0_16, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.36/0.55  fof(c_0_17, plain, ![X35, X36, X37, X38]:((((r2_hidden(u1_struct_0(X35),u1_pre_topc(X35))|~v2_pre_topc(X35)|~l1_pre_topc(X35))&(~m1_subset_1(X36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|(~r1_tarski(X36,u1_pre_topc(X35))|r2_hidden(k5_setfam_1(u1_struct_0(X35),X36),u1_pre_topc(X35)))|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X35)))|(~r2_hidden(X37,u1_pre_topc(X35))|~r2_hidden(X38,u1_pre_topc(X35))|r2_hidden(k9_subset_1(u1_struct_0(X35),X37,X38),u1_pre_topc(X35))))|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(((m1_subset_1(esk7_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&((m1_subset_1(esk8_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(((r2_hidden(esk7_1(X35),u1_pre_topc(X35))|(m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(r2_hidden(esk8_1(X35),u1_pre_topc(X35))|(m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r2_hidden(k9_subset_1(u1_struct_0(X35),esk7_1(X35),esk8_1(X35)),u1_pre_topc(X35))|(m1_subset_1(esk6_1(X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X35))))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))))&(((m1_subset_1(esk7_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(r1_tarski(esk6_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&((m1_subset_1(esk8_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(r1_tarski(esk6_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(((r2_hidden(esk7_1(X35),u1_pre_topc(X35))|(r1_tarski(esk6_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(r2_hidden(esk8_1(X35),u1_pre_topc(X35))|(r1_tarski(esk6_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r2_hidden(k9_subset_1(u1_struct_0(X35),esk7_1(X35),esk8_1(X35)),u1_pre_topc(X35))|(r1_tarski(esk6_1(X35),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))))&((m1_subset_1(esk7_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&((m1_subset_1(esk8_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(((r2_hidden(esk7_1(X35),u1_pre_topc(X35))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35))&(r2_hidden(esk8_1(X35),u1_pre_topc(X35))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r2_hidden(k9_subset_1(u1_struct_0(X35),esk7_1(X35),esk8_1(X35)),u1_pre_topc(X35))|(~r2_hidden(k5_setfam_1(u1_struct_0(X35),esk6_1(X35)),u1_pre_topc(X35))|~r2_hidden(u1_struct_0(X35),u1_pre_topc(X35)))|v2_pre_topc(X35)|~l1_pre_topc(X35)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.36/0.55  fof(c_0_18, plain, ![X43]:(v1_xboole_0(X43)|(~r2_hidden(k3_tarski(X43),X43)|k4_yellow_0(k2_yellow_1(X43))=k3_tarski(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.36/0.55  fof(c_0_19, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.36/0.55  cnf(c_0_20, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.36/0.55  cnf(c_0_21, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.36/0.55  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.36/0.55  fof(c_0_23, plain, ![X30, X31]:((~m1_subset_1(X30,k1_zfmisc_1(X31))|r1_tarski(X30,X31))&(~r1_tarski(X30,X31)|m1_subset_1(X30,k1_zfmisc_1(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.36/0.55  cnf(c_0_24, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.36/0.55  fof(c_0_25, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.36/0.55  cnf(c_0_26, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_16])).
% 0.36/0.55  cnf(c_0_27, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.36/0.55  fof(c_0_28, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.36/0.55  cnf(c_0_29, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.36/0.55  cnf(c_0_30, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.36/0.55  cnf(c_0_31, plain, (r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.36/0.55  cnf(c_0_32, plain, (k5_setfam_1(u1_struct_0(X1),u1_pre_topc(X1))=k3_tarski(u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.36/0.55  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.36/0.55  cnf(c_0_34, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.36/0.55  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.36/0.55  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.36/0.55  cnf(c_0_37, plain, (r2_hidden(X1,k3_tarski(u1_pre_topc(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.36/0.55  fof(c_0_38, negated_conjecture, (((~v2_struct_0(esk9_0)&v2_pre_topc(esk9_0))&l1_pre_topc(esk9_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0)))!=u1_struct_0(esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_28])])])])).
% 0.36/0.55  cnf(c_0_39, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_29, c_0_30])).
% 0.36/0.55  cnf(c_0_40, plain, (r2_hidden(k3_tarski(u1_pre_topc(X1)),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), c_0_21])).
% 0.36/0.55  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.36/0.55  cnf(c_0_42, plain, (r1_tarski(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.36/0.55  cnf(c_0_43, plain, (r1_tarski(X1,k3_tarski(u1_pre_topc(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(esk2_2(X1,k3_tarski(u1_pre_topc(X2))),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.36/0.55  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.36/0.55  cnf(c_0_45, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk9_0)))!=u1_struct_0(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.36/0.55  cnf(c_0_46, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=k3_tarski(u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.36/0.55  cnf(c_0_47, negated_conjecture, (v2_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.36/0.55  cnf(c_0_48, negated_conjecture, (l1_pre_topc(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.36/0.55  cnf(c_0_49, plain, (u1_struct_0(X1)=X2|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),X2)|~r2_hidden(X2,u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.36/0.55  cnf(c_0_50, plain, (r1_tarski(u1_struct_0(X1),k3_tarski(u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.36/0.55  cnf(c_0_51, negated_conjecture, (k3_tarski(u1_pre_topc(esk9_0))!=u1_struct_0(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])])).
% 0.36/0.55  cnf(c_0_52, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_40])).
% 0.36/0.55  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_47]), c_0_48])]), ['proof']).
% 0.36/0.55  # SZS output end CNFRefutation
% 0.36/0.55  # Proof object total steps             : 54
% 0.36/0.55  # Proof object clause steps            : 31
% 0.36/0.55  # Proof object formula steps           : 23
% 0.36/0.55  # Proof object conjectures             : 8
% 0.36/0.55  # Proof object clause conjectures      : 5
% 0.36/0.55  # Proof object formula conjectures     : 3
% 0.36/0.55  # Proof object initial clauses used    : 16
% 0.36/0.55  # Proof object initial formulas used   : 11
% 0.36/0.55  # Proof object generating inferences   : 12
% 0.36/0.55  # Proof object simplifying inferences  : 13
% 0.36/0.55  # Training examples: 0 positive, 0 negative
% 0.36/0.55  # Parsed axioms                        : 11
% 0.36/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.36/0.55  # Initial clauses                      : 42
% 0.36/0.55  # Removed in clause preprocessing      : 0
% 0.36/0.55  # Initial clauses in saturation        : 42
% 0.36/0.55  # Processed clauses                    : 1633
% 0.36/0.55  # ...of these trivial                  : 0
% 0.36/0.55  # ...subsumed                          : 1216
% 0.36/0.55  # ...remaining for further processing  : 417
% 0.36/0.55  # Other redundant clauses eliminated   : 5
% 0.36/0.55  # Clauses deleted for lack of memory   : 0
% 0.36/0.55  # Backward-subsumed                    : 9
% 0.36/0.55  # Backward-rewritten                   : 0
% 0.36/0.55  # Generated clauses                    : 12833
% 0.36/0.55  # ...of the previous two non-trivial   : 12785
% 0.36/0.55  # Contextual simplify-reflections      : 18
% 0.36/0.55  # Paramodulations                      : 12828
% 0.36/0.55  # Factorizations                       : 0
% 0.36/0.55  # Equation resolutions                 : 5
% 0.36/0.55  # Propositional unsat checks           : 0
% 0.36/0.55  #    Propositional check models        : 0
% 0.36/0.55  #    Propositional check unsatisfiable : 0
% 0.36/0.55  #    Propositional clauses             : 0
% 0.36/0.55  #    Propositional clauses after purity: 0
% 0.36/0.55  #    Propositional unsat core size     : 0
% 0.36/0.55  #    Propositional preprocessing time  : 0.000
% 0.36/0.55  #    Propositional encoding time       : 0.000
% 0.36/0.55  #    Propositional solver time         : 0.000
% 0.36/0.55  #    Success case prop preproc time    : 0.000
% 0.36/0.55  #    Success case prop encoding time   : 0.000
% 0.36/0.55  #    Success case prop solver time     : 0.000
% 0.36/0.55  # Current number of processed clauses  : 362
% 0.36/0.55  #    Positive orientable unit clauses  : 4
% 0.36/0.55  #    Positive unorientable unit clauses: 0
% 0.36/0.55  #    Negative unit clauses             : 4
% 0.36/0.55  #    Non-unit-clauses                  : 354
% 0.36/0.55  # Current number of unprocessed clauses: 11114
% 0.36/0.55  # ...number of literals in the above   : 47201
% 0.36/0.55  # Current number of archived formulas  : 0
% 0.36/0.55  # Current number of archived clauses   : 50
% 0.36/0.55  # Clause-clause subsumption calls (NU) : 42511
% 0.36/0.55  # Rec. Clause-clause subsumption calls : 19588
% 0.36/0.55  # Non-unit clause-clause subsumptions  : 1242
% 0.36/0.55  # Unit Clause-clause subsumption calls : 82
% 0.36/0.55  # Rewrite failures with RHS unbound    : 0
% 0.36/0.55  # BW rewrite match attempts            : 0
% 0.36/0.55  # BW rewrite match successes           : 0
% 0.36/0.55  # Condensation attempts                : 0
% 0.36/0.55  # Condensation successes               : 0
% 0.36/0.55  # Termbank termtop insertions          : 214344
% 0.36/0.55  
% 0.36/0.55  # -------------------------------------------------
% 0.36/0.55  # User time                : 0.188 s
% 0.36/0.55  # System time              : 0.011 s
% 0.36/0.55  # Total time               : 0.199 s
% 0.36/0.55  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

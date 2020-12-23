%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:15 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 115 expanded)
%              Number of clauses        :   36 (  52 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  206 ( 438 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
               => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_tops_2])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | r1_tarski(X13,X11)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r1_tarski(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r1_tarski(esk2_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(esk2_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    & m1_pre_topc(esk7_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
    & ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X21,X22,X23,X25,X27] :
      ( ( r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk3_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk3_3(X21,X22,X23),u1_pre_topc(X21))
        | ~ r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( X23 = k9_subset_1(u1_struct_0(X22),esk3_3(X21,X22,X23),k2_struct_0(X22))
        | ~ r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X25,u1_pre_topc(X21))
        | X23 != k9_subset_1(u1_struct_0(X22),X25,k2_struct_0(X22))
        | r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk4_2(X21,X22),k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(esk4_2(X21,X22),u1_pre_topc(X22))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X27,u1_pre_topc(X21))
        | esk4_2(X21,X22) != k9_subset_1(u1_struct_0(X22),X27,k2_struct_0(X22))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk5_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | r2_hidden(esk4_2(X21,X22),u1_pre_topc(X22))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk5_2(X21,X22),u1_pre_topc(X21))
        | r2_hidden(esk4_2(X21,X22),u1_pre_topc(X22))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( esk4_2(X21,X22) = k9_subset_1(u1_struct_0(X22),esk5_2(X21,X22),k2_struct_0(X22))
        | r2_hidden(esk4_2(X21,X22),u1_pre_topc(X22))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_19,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | l1_pre_topc(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

fof(c_0_27,plain,(
    ! [X20] :
      ( ~ l1_struct_0(X20)
      | k2_struct_0(X20) = u1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_28,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk1_2(esk8_0,X1),X2),u1_struct_0(esk7_0))
    | r1_tarski(esk1_2(esk8_0,X1),X2)
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(k2_struct_0(X1),X2),k2_struct_0(X3))
    | r1_tarski(k2_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(esk1_2(esk8_0,X1),X2),X3)
    | r1_tarski(esk1_2(esk8_0,X1),X2)
    | r1_tarski(esk8_0,X1)
    | ~ r1_tarski(u1_struct_0(esk7_0),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_30])).

cnf(c_0_37,plain,
    ( u1_struct_0(X1) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_33]),c_0_34])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_2(k2_struct_0(esk7_0),X1),k2_struct_0(esk6_0))
    | r1_tarski(k2_struct_0(esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(esk1_2(esk8_0,X1),X2),X3)
    | r1_tarski(esk1_2(esk8_0,X1),X2)
    | r1_tarski(esk8_0,X1)
    | ~ r1_tarski(k2_struct_0(esk7_0),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk7_0),k2_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(esk1_2(esk8_0,X1),X2),k2_struct_0(esk6_0))
    | r1_tarski(esk1_2(esk8_0,X1),X2)
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk1_2(esk8_0,X1),k2_struct_0(esk6_0))
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_37]),c_0_34])])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,X1),k1_zfmisc_1(k2_struct_0(esk6_0)))
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(esk8_0,k1_zfmisc_1(k2_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t31_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.19/0.41  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.41  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.41  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))))), inference(assume_negation,[status(cth)],[t31_tops_2])).
% 0.19/0.41  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.41  fof(c_0_10, plain, ![X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X13,X12)|r1_tarski(X13,X11)|X12!=k1_zfmisc_1(X11))&(~r1_tarski(X14,X11)|r2_hidden(X14,X12)|X12!=k1_zfmisc_1(X11)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.41  fof(c_0_11, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  fof(c_0_12, negated_conjecture, (l1_pre_topc(esk6_0)&(m1_pre_topc(esk7_0,esk6_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))&~m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.41  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_18, plain, ![X21, X22, X23, X25, X27]:(((r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&((((m1_subset_1(esk3_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|~r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(r2_hidden(esk3_3(X21,X22,X23),u1_pre_topc(X21))|~r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(X23=k9_subset_1(u1_struct_0(X22),esk3_3(X21,X22,X23),k2_struct_0(X22))|~r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X21)))|~r2_hidden(X25,u1_pre_topc(X21))|X23!=k9_subset_1(u1_struct_0(X22),X25,k2_struct_0(X22))|r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))))&((m1_subset_1(esk4_2(X21,X22),k1_zfmisc_1(u1_struct_0(X22)))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&((~r2_hidden(esk4_2(X21,X22),u1_pre_topc(X22))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X21)))|~r2_hidden(X27,u1_pre_topc(X21))|esk4_2(X21,X22)!=k9_subset_1(u1_struct_0(X22),X27,k2_struct_0(X22)))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(((m1_subset_1(esk5_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))|r2_hidden(esk4_2(X21,X22),u1_pre_topc(X22))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(r2_hidden(esk5_2(X21,X22),u1_pre_topc(X21))|r2_hidden(esk4_2(X21,X22),u1_pre_topc(X22))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(esk4_2(X21,X22)=k9_subset_1(u1_struct_0(X22),esk5_2(X21,X22),k2_struct_0(X22))|r2_hidden(esk4_2(X21,X22),u1_pre_topc(X22))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.19/0.41  fof(c_0_19, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|l1_pre_topc(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.41  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.41  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_22, negated_conjecture, (r1_tarski(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.41  cnf(c_0_23, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(esk8_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0)))|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.19/0.41  fof(c_0_27, plain, ![X20]:(~l1_struct_0(X20)|k2_struct_0(X20)=u1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.41  fof(c_0_28, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.41  cnf(c_0_29, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk1_2(esk8_0,X1),X2),u1_struct_0(esk7_0))|r1_tarski(esk1_2(esk8_0,X1),X2)|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.41  cnf(c_0_31, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_32, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_35, plain, (r2_hidden(esk1_2(k2_struct_0(X1),X2),k2_struct_0(X3))|r1_tarski(k2_struct_0(X1),X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(spm,[status(thm)],[c_0_20, c_0_29])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(esk1_2(esk8_0,X1),X2),X3)|r1_tarski(esk1_2(esk8_0,X1),X2)|r1_tarski(esk8_0,X1)|~r1_tarski(u1_struct_0(esk7_0),X3)), inference(spm,[status(thm)],[c_0_13, c_0_30])).
% 0.19/0.41  cnf(c_0_37, plain, (u1_struct_0(X1)=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_33]), c_0_34])])).
% 0.19/0.41  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_2(k2_struct_0(esk7_0),X1),k2_struct_0(esk6_0))|r1_tarski(k2_struct_0(esk7_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33]), c_0_34])])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(esk1_2(esk8_0,X1),X2),X3)|r1_tarski(esk1_2(esk8_0,X1),X2)|r1_tarski(esk8_0,X1)|~r1_tarski(k2_struct_0(esk7_0),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_struct_0(esk7_0),k2_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.41  cnf(c_0_43, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(esk1_2(esk8_0,X1),X2),k2_struct_0(esk6_0))|r1_tarski(esk1_2(esk8_0,X1),X2)|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_46, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (r1_tarski(esk1_2(esk8_0,X1),k2_struct_0(esk6_0))|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_44])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_37]), c_0_34])])).
% 0.19/0.41  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_2(esk8_0,X1),k1_zfmisc_1(k2_struct_0(esk6_0)))|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (~r1_tarski(esk8_0,k1_zfmisc_1(k2_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_50]), c_0_51]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 53
% 0.19/0.41  # Proof object clause steps            : 36
% 0.19/0.41  # Proof object formula steps           : 17
% 0.19/0.41  # Proof object conjectures             : 21
% 0.19/0.41  # Proof object clause conjectures      : 18
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 15
% 0.19/0.41  # Proof object initial formulas used   : 8
% 0.19/0.41  # Proof object generating inferences   : 18
% 0.19/0.41  # Proof object simplifying inferences  : 12
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 8
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 26
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 26
% 0.19/0.41  # Processed clauses                    : 441
% 0.19/0.41  # ...of these trivial                  : 2
% 0.19/0.41  # ...subsumed                          : 166
% 0.19/0.41  # ...remaining for further processing  : 273
% 0.19/0.41  # Other redundant clauses eliminated   : 3
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 0
% 0.19/0.41  # Generated clauses                    : 807
% 0.19/0.41  # ...of the previous two non-trivial   : 764
% 0.19/0.41  # Contextual simplify-reflections      : 12
% 0.19/0.41  # Paramodulations                      : 800
% 0.19/0.41  # Factorizations                       : 4
% 0.19/0.41  # Equation resolutions                 : 3
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 244
% 0.19/0.41  #    Positive orientable unit clauses  : 13
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 6
% 0.19/0.41  #    Non-unit-clauses                  : 225
% 0.19/0.41  # Current number of unprocessed clauses: 370
% 0.19/0.41  # ...number of literals in the above   : 2147
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 26
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 11371
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 3633
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 176
% 0.19/0.41  # Unit Clause-clause subsumption calls : 21
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 20
% 0.19/0.41  # BW rewrite match successes           : 0
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 21739
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.067 s
% 0.19/0.41  # System time              : 0.003 s
% 0.19/0.41  # Total time               : 0.070 s
% 0.19/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

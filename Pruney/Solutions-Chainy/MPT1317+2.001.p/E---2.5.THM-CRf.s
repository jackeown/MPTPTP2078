%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:21 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 189 expanded)
%              Number of clauses        :   34 (  71 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  184 ( 959 expanded)
%              Number of equality atoms :   13 ( 107 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v4_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(t36_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v2_tops_2(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
                   => ( X4 = X2
                     => v2_tops_2(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tops_2)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(c_0_7,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_pre_topc(X28,X26)
      | ~ v4_pre_topc(X27,X26)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | X29 != X27
      | v4_pre_topc(X29,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_tops_2])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( v2_tops_2(X2,X1)
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
                     => ( X4 = X2
                       => v2_tops_2(X4,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_tops_2])).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_12,plain,
    ( v4_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & m1_pre_topc(esk6_0,esk4_0)
    & v2_tops_2(esk5_0,esk4_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
    & esk7_0 = esk5_0
    & ~ v2_tops_2(esk7_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_14,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | l1_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_tops_2(X23,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X24,X23)
        | v4_pre_topc(X24,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk3_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | v2_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | v2_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( ~ v4_pre_topc(esk3_2(X22,X23),X22)
        | v2_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_19,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( esk7_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_tops_2(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v4_pre_topc(X1,esk6_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( v2_tops_2(X1,esk6_0)
    | ~ v4_pre_topc(esk3_2(esk6_0,X1),esk4_0)
    | ~ m1_subset_1(esk3_2(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(esk3_2(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_39,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_2(esk6_0,esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32])]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v2_tops_2(X1,esk6_0)
    | ~ v2_tops_2(X2,esk4_0)
    | ~ m1_subset_1(esk3_2(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(esk3_2(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ r2_hidden(esk3_2(esk6_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_21])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_32])]),c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_2(esk6_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_tops_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ r2_hidden(esk3_2(esk6_0,esk5_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_36])]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_26]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:39:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.15/3.33  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04AI
% 3.15/3.33  # and selection function SelectComplexExceptUniqMaxHorn.
% 3.15/3.33  #
% 3.15/3.33  # Preprocessing time       : 0.028 s
% 3.15/3.33  # Presaturation interreduction done
% 3.15/3.33  
% 3.15/3.33  # Proof found!
% 3.15/3.33  # SZS status Theorem
% 3.15/3.33  # SZS output start CNFRefutation
% 3.15/3.33  fof(t34_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 3.15/3.33  fof(t36_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v2_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v2_tops_2(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tops_2)).
% 3.15/3.33  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.15/3.33  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.15/3.33  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.15/3.33  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.15/3.33  fof(d2_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 3.15/3.33  fof(c_0_7, plain, ![X26, X27, X28, X29]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_pre_topc(X28,X26)|(~v4_pre_topc(X27,X26)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(X29!=X27|v4_pre_topc(X29,X28))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_tops_2])])])).
% 3.15/3.33  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v2_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v2_tops_2(X4,X3)))))))), inference(assume_negation,[status(cth)],[t36_tops_2])).
% 3.15/3.33  fof(c_0_9, plain, ![X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X13,X12)|r1_tarski(X13,X11)|X12!=k1_zfmisc_1(X11))&(~r1_tarski(X14,X11)|r2_hidden(X14,X12)|X12!=k1_zfmisc_1(X11)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 3.15/3.33  fof(c_0_10, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 3.15/3.33  fof(c_0_11, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.15/3.33  cnf(c_0_12, plain, (v4_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v4_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_7])).
% 3.15/3.33  fof(c_0_13, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(m1_pre_topc(esk6_0,esk4_0)&(v2_tops_2(esk5_0,esk4_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))&(esk7_0=esk5_0&~v2_tops_2(esk7_0,esk6_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 3.15/3.33  fof(c_0_14, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|l1_pre_topc(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 3.15/3.33  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.15/3.33  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 3.15/3.33  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.15/3.33  fof(c_0_18, plain, ![X22, X23, X24]:((~v2_tops_2(X23,X22)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(~r2_hidden(X24,X23)|v4_pre_topc(X24,X22)))|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&((m1_subset_1(esk3_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|v2_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&((r2_hidden(esk3_2(X22,X23),X23)|v2_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&(~v4_pre_topc(esk3_2(X22,X23),X22)|v2_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).
% 3.15/3.33  cnf(c_0_19, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_12])).
% 3.15/3.33  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.15/3.33  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.15/3.33  cnf(c_0_22, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.15/3.33  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.15/3.33  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_15])).
% 3.15/3.33  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 3.15/3.33  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.15/3.33  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.15/3.33  cnf(c_0_28, negated_conjecture, (esk7_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.15/3.33  cnf(c_0_29, negated_conjecture, (~v2_tops_2(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.15/3.33  cnf(c_0_30, plain, (v2_tops_2(X2,X1)|~v4_pre_topc(esk3_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.15/3.33  cnf(c_0_31, negated_conjecture, (v4_pre_topc(X1,esk6_0)|~v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 3.15/3.33  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_21])])).
% 3.15/3.33  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 3.15/3.33  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 3.15/3.33  cnf(c_0_35, plain, (r2_hidden(esk3_2(X1,X2),X2)|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.15/3.33  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 3.15/3.33  cnf(c_0_37, negated_conjecture, (~v2_tops_2(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 3.15/3.33  cnf(c_0_38, negated_conjecture, (v2_tops_2(X1,esk6_0)|~v4_pre_topc(esk3_2(esk6_0,X1),esk4_0)|~m1_subset_1(esk3_2(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(esk3_2(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 3.15/3.33  cnf(c_0_39, plain, (v4_pre_topc(X3,X2)|~v2_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.15/3.33  cnf(c_0_40, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.15/3.33  cnf(c_0_41, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 3.15/3.33  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_2(esk6_0,esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32])]), c_0_37])).
% 3.15/3.33  cnf(c_0_43, negated_conjecture, (v2_tops_2(X1,esk6_0)|~v2_tops_2(X2,esk4_0)|~m1_subset_1(esk3_2(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(esk3_2(esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|~r2_hidden(esk3_2(esk6_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_21])])).
% 3.15/3.33  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_32])]), c_0_37])).
% 3.15/3.33  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk3_2(esk6_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 3.15/3.33  cnf(c_0_46, negated_conjecture, (~v2_tops_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|~r2_hidden(esk3_2(esk6_0,esk5_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_36])]), c_0_37])).
% 3.15/3.33  cnf(c_0_47, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.15/3.33  cnf(c_0_48, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_26]), c_0_42])]), ['proof']).
% 3.15/3.33  # SZS output end CNFRefutation
% 3.15/3.33  # Proof object total steps             : 49
% 3.15/3.33  # Proof object clause steps            : 34
% 3.15/3.33  # Proof object formula steps           : 15
% 3.15/3.33  # Proof object conjectures             : 23
% 3.15/3.33  # Proof object clause conjectures      : 20
% 3.15/3.33  # Proof object formula conjectures     : 3
% 3.15/3.33  # Proof object initial clauses used    : 17
% 3.15/3.33  # Proof object initial formulas used   : 7
% 3.15/3.33  # Proof object generating inferences   : 13
% 3.15/3.33  # Proof object simplifying inferences  : 25
% 3.15/3.33  # Training examples: 0 positive, 0 negative
% 3.15/3.33  # Parsed axioms                        : 7
% 3.15/3.33  # Removed by relevancy pruning/SinE    : 0
% 3.15/3.33  # Initial clauses                      : 22
% 3.15/3.33  # Removed in clause preprocessing      : 0
% 3.15/3.33  # Initial clauses in saturation        : 22
% 3.15/3.33  # Processed clauses                    : 5079
% 3.15/3.33  # ...of these trivial                  : 2
% 3.15/3.33  # ...subsumed                          : 2337
% 3.15/3.33  # ...remaining for further processing  : 2740
% 3.15/3.33  # Other redundant clauses eliminated   : 3
% 3.15/3.33  # Clauses deleted for lack of memory   : 0
% 3.15/3.33  # Backward-subsumed                    : 37
% 3.15/3.33  # Backward-rewritten                   : 1
% 3.15/3.33  # Generated clauses                    : 436817
% 3.15/3.33  # ...of the previous two non-trivial   : 409922
% 3.15/3.33  # Contextual simplify-reflections      : 17
% 3.15/3.33  # Paramodulations                      : 436588
% 3.15/3.33  # Factorizations                       : 226
% 3.15/3.33  # Equation resolutions                 : 3
% 3.15/3.33  # Propositional unsat checks           : 0
% 3.15/3.33  #    Propositional check models        : 0
% 3.15/3.33  #    Propositional check unsatisfiable : 0
% 3.15/3.33  #    Propositional clauses             : 0
% 3.15/3.33  #    Propositional clauses after purity: 0
% 3.15/3.33  #    Propositional unsat core size     : 0
% 3.15/3.33  #    Propositional preprocessing time  : 0.000
% 3.15/3.33  #    Propositional encoding time       : 0.000
% 3.15/3.33  #    Propositional solver time         : 0.000
% 3.15/3.33  #    Success case prop preproc time    : 0.000
% 3.15/3.33  #    Success case prop encoding time   : 0.000
% 3.15/3.33  #    Success case prop solver time     : 0.000
% 3.15/3.33  # Current number of processed clauses  : 2677
% 3.15/3.33  #    Positive orientable unit clauses  : 18
% 3.15/3.33  #    Positive unorientable unit clauses: 0
% 3.15/3.33  #    Negative unit clauses             : 1
% 3.15/3.33  #    Non-unit-clauses                  : 2658
% 3.15/3.33  # Current number of unprocessed clauses: 404865
% 3.15/3.33  # ...number of literals in the above   : 2062821
% 3.15/3.33  # Current number of archived formulas  : 0
% 3.15/3.33  # Current number of archived clauses   : 60
% 3.15/3.33  # Clause-clause subsumption calls (NU) : 1286361
% 3.15/3.33  # Rec. Clause-clause subsumption calls : 249259
% 3.15/3.33  # Non-unit clause-clause subsumptions  : 2388
% 3.15/3.33  # Unit Clause-clause subsumption calls : 110
% 3.15/3.33  # Rewrite failures with RHS unbound    : 0
% 3.15/3.33  # BW rewrite match attempts            : 28
% 3.15/3.33  # BW rewrite match successes           : 1
% 3.15/3.33  # Condensation attempts                : 0
% 3.15/3.33  # Condensation successes               : 0
% 3.15/3.33  # Termbank termtop insertions          : 12196276
% 3.15/3.34  
% 3.15/3.34  # -------------------------------------------------
% 3.15/3.34  # User time                : 2.880 s
% 3.15/3.34  # System time              : 0.125 s
% 3.15/3.34  # Total time               : 3.005 s
% 3.15/3.34  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

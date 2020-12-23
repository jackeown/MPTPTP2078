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
% DateTime   : Thu Dec  3 11:09:30 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 117 expanded)
%              Number of clauses        :   31 (  47 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  214 ( 599 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d8_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r8_relat_2(X1,X2)
        <=> ! [X3,X4,X5] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(X5,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X5),X1) )
             => r2_hidden(k4_tarski(X3,X5),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d5_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v4_orders_2(X1)
      <=> r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

fof(t26_orders_2,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_10,plain,(
    ! [X30] :
      ( ~ l1_orders_2(X30)
      | m1_subset_1(u1_orders_2(X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X30)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_11,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_12,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ r2_hidden(X12,X11)
      | r2_hidden(X12,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_13,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r8_relat_2(X17,X18)
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X21,X18)
        | ~ r2_hidden(k4_tarski(X19,X20),X17)
        | ~ r2_hidden(k4_tarski(X20,X21),X17)
        | r2_hidden(k4_tarski(X19,X21),X17)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk1_2(X17,X22),X22)
        | r8_relat_2(X17,X22)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk2_2(X17,X22),X22)
        | r8_relat_2(X17,X22)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk3_2(X17,X22),X22)
        | r8_relat_2(X17,X22)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(k4_tarski(esk1_2(X17,X22),esk2_2(X17,X22)),X17)
        | r8_relat_2(X17,X22)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(k4_tarski(esk2_2(X17,X22),esk3_2(X17,X22)),X17)
        | r8_relat_2(X17,X22)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X17,X22),esk3_2(X17,X22)),X17)
        | r8_relat_2(X17,X22)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

fof(c_0_14,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_orders_2(X27,X28,X29)
        | r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))
        | r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_15,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X6,X7,X8,X9] :
      ( ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X7,X9)
        | r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X3,X5),X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X5,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X1,u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r1_orders_2(X3,X4,X2)
    | ~ l1_orders_2(X3)
    | ~ r8_relat_2(u1_orders_2(X3),X5)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ r2_hidden(k4_tarski(X1,X4),u1_orders_2(X3))
    | ~ r2_hidden(X2,X5)
    | ~ r2_hidden(X4,X5)
    | ~ r2_hidden(X1,X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_27,plain,(
    ! [X26] :
      ( ( ~ v4_orders_2(X26)
        | r8_relat_2(u1_orders_2(X26),u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( ~ r8_relat_2(u1_orders_2(X26),u1_struct_0(X26))
        | v4_orders_2(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X3,X4) )
                     => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_orders_2])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r1_orders_2(X3,X4,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ l1_orders_2(X3)
    | ~ r8_relat_2(u1_orders_2(X3),X5)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X2,X5)
    | ~ r2_hidden(X4,X5)
    | ~ r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_32,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

fof(c_0_35,negated_conjecture,
    ( v4_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & r1_orders_2(esk4_0,esk5_0,esk6_0)
    & r1_orders_2(esk4_0,esk6_0,esk7_0)
    & ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r1_orders_2(X3,X4,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(esk4_0,X2,esk7_0)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk7_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39]),c_0_37])])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:14:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.027 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.39  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.12/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.12/0.39  fof(d8_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r8_relat_2(X1,X2)<=>![X3, X4, X5]:(((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&r2_hidden(X5,X2))&r2_hidden(k4_tarski(X3,X4),X1))&r2_hidden(k4_tarski(X4,X5),X1))=>r2_hidden(k4_tarski(X3,X5),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_2)).
% 0.12/0.39  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.12/0.39  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.12/0.39  fof(d5_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v4_orders_2(X1)<=>r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_orders_2)).
% 0.12/0.39  fof(t26_orders_2, conjecture, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 0.12/0.39  fof(c_0_9, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.39  fof(c_0_10, plain, ![X30]:(~l1_orders_2(X30)|m1_subset_1(u1_orders_2(X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X30))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.12/0.39  fof(c_0_11, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.39  fof(c_0_12, plain, ![X10, X11, X12]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|(~r2_hidden(X12,X11)|r2_hidden(X12,X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.12/0.39  fof(c_0_13, plain, ![X17, X18, X19, X20, X21, X22]:((~r8_relat_2(X17,X18)|(~r2_hidden(X19,X18)|~r2_hidden(X20,X18)|~r2_hidden(X21,X18)|~r2_hidden(k4_tarski(X19,X20),X17)|~r2_hidden(k4_tarski(X20,X21),X17)|r2_hidden(k4_tarski(X19,X21),X17))|~v1_relat_1(X17))&((((((r2_hidden(esk1_2(X17,X22),X22)|r8_relat_2(X17,X22)|~v1_relat_1(X17))&(r2_hidden(esk2_2(X17,X22),X22)|r8_relat_2(X17,X22)|~v1_relat_1(X17)))&(r2_hidden(esk3_2(X17,X22),X22)|r8_relat_2(X17,X22)|~v1_relat_1(X17)))&(r2_hidden(k4_tarski(esk1_2(X17,X22),esk2_2(X17,X22)),X17)|r8_relat_2(X17,X22)|~v1_relat_1(X17)))&(r2_hidden(k4_tarski(esk2_2(X17,X22),esk3_2(X17,X22)),X17)|r8_relat_2(X17,X22)|~v1_relat_1(X17)))&(~r2_hidden(k4_tarski(esk1_2(X17,X22),esk3_2(X17,X22)),X17)|r8_relat_2(X17,X22)|~v1_relat_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).
% 0.12/0.39  fof(c_0_14, plain, ![X27, X28, X29]:((~r1_orders_2(X27,X28,X29)|r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))&(~r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))|r1_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.12/0.39  cnf(c_0_15, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_16, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_17, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  fof(c_0_18, plain, ![X6, X7, X8, X9]:(((r2_hidden(X6,X8)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))&(r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9))))&(~r2_hidden(X6,X8)|~r2_hidden(X7,X9)|r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.12/0.39  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X3,X5),X1)|~r8_relat_2(X1,X2)|~r2_hidden(X3,X2)|~r2_hidden(X4,X2)|~r2_hidden(X5,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~r2_hidden(k4_tarski(X4,X5),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_22, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.12/0.39  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_24, plain, (r2_hidden(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))|~l1_orders_2(X2)|~r2_hidden(X1,u1_orders_2(X2))), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 0.12/0.39  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~r1_orders_2(X3,X4,X2)|~l1_orders_2(X3)|~r8_relat_2(u1_orders_2(X3),X5)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X3))|~r2_hidden(k4_tarski(X1,X4),u1_orders_2(X3))|~r2_hidden(X2,X5)|~r2_hidden(X4,X5)|~r2_hidden(X1,X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.12/0.39  fof(c_0_27, plain, ![X26]:((~v4_orders_2(X26)|r8_relat_2(u1_orders_2(X26),u1_struct_0(X26))|~l1_orders_2(X26))&(~r8_relat_2(u1_orders_2(X26),u1_struct_0(X26))|v4_orders_2(X26)|~l1_orders_2(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).
% 0.12/0.39  cnf(c_0_28, plain, (r2_hidden(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~r2_hidden(k4_tarski(X1,X3),u1_orders_2(X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.39  cnf(c_0_29, plain, (r2_hidden(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~r2_hidden(k4_tarski(X3,X1),u1_orders_2(X2))), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.12/0.39  fof(c_0_30, negated_conjecture, ~(![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t26_orders_2])).
% 0.12/0.39  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~r1_orders_2(X3,X4,X2)|~r1_orders_2(X3,X1,X4)|~l1_orders_2(X3)|~r8_relat_2(u1_orders_2(X3),X5)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X2,X5)|~r2_hidden(X4,X5)|~r2_hidden(X1,X5)), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.12/0.39  cnf(c_0_32, plain, (r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.39  cnf(c_0_33, plain, (r2_hidden(X1,u1_struct_0(X2))|~r1_orders_2(X2,X1,X3)|~l1_orders_2(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 0.12/0.39  cnf(c_0_34, plain, (r2_hidden(X1,u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~l1_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.12/0.39  fof(c_0_35, negated_conjecture, ((v4_orders_2(esk4_0)&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&((r1_orders_2(esk4_0,esk5_0,esk6_0)&r1_orders_2(esk4_0,esk6_0,esk7_0))&~r1_orders_2(esk4_0,esk5_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.12/0.39  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~r1_orders_2(X3,X4,X2)|~r1_orders_2(X3,X1,X4)|~v4_orders_2(X3)|~l1_orders_2(X3)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_34])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))|~r1_orders_2(esk4_0,X2,esk7_0)|~r1_orders_2(esk4_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_43, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))|~r1_orders_2(esk4_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.12/0.39  cnf(c_0_45, negated_conjecture, (~r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (r1_orders_2(esk4_0,X1,esk7_0)|~r1_orders_2(esk4_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39]), c_0_37])])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 50
% 0.12/0.39  # Proof object clause steps            : 31
% 0.12/0.39  # Proof object formula steps           : 19
% 0.12/0.39  # Proof object conjectures             : 15
% 0.12/0.39  # Proof object clause conjectures      : 12
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 18
% 0.12/0.39  # Proof object initial formulas used   : 9
% 0.12/0.39  # Proof object generating inferences   : 13
% 0.12/0.39  # Proof object simplifying inferences  : 17
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 9
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 26
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 26
% 0.12/0.39  # Processed clauses                    : 178
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 10
% 0.12/0.39  # ...remaining for further processing  : 168
% 0.12/0.39  # Other redundant clauses eliminated   : 0
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 15
% 0.12/0.39  # Backward-rewritten                   : 17
% 0.12/0.39  # Generated clauses                    : 297
% 0.12/0.39  # ...of the previous two non-trivial   : 221
% 0.12/0.39  # Contextual simplify-reflections      : 8
% 0.12/0.39  # Paramodulations                      : 297
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 0
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 110
% 0.12/0.39  #    Positive orientable unit clauses  : 21
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 1
% 0.12/0.39  #    Non-unit-clauses                  : 88
% 0.12/0.39  # Current number of unprocessed clauses: 76
% 0.12/0.39  # ...number of literals in the above   : 410
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 58
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1975
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 676
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 23
% 0.12/0.39  # Unit Clause-clause subsumption calls : 100
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 24
% 0.12/0.39  # BW rewrite match successes           : 17
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 11629
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.044 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.048 s
% 0.12/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

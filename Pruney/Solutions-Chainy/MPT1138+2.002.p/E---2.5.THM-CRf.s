%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 114 expanded)
%              Number of clauses        :   30 (  46 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  208 ( 593 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

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

fof(c_0_8,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_9,plain,(
    ! [X29] :
      ( ~ l1_orders_2(X29)
      | m1_subset_1(u1_orders_2(X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X29)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_10,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ r2_hidden(X12,X11)
      | r2_hidden(X12,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_11,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r8_relat_2(X16,X17)
        | ~ r2_hidden(X18,X17)
        | ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X20,X17)
        | ~ r2_hidden(k4_tarski(X18,X19),X16)
        | ~ r2_hidden(k4_tarski(X19,X20),X16)
        | r2_hidden(k4_tarski(X18,X20),X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk1_2(X16,X21),X21)
        | r8_relat_2(X16,X21)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk2_2(X16,X21),X21)
        | r8_relat_2(X16,X21)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk3_2(X16,X21),X21)
        | r8_relat_2(X16,X21)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk1_2(X16,X21),esk2_2(X16,X21)),X16)
        | r8_relat_2(X16,X21)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk2_2(X16,X21),esk3_2(X16,X21)),X16)
        | r8_relat_2(X16,X21)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X16,X21),esk3_2(X16,X21)),X16)
        | r8_relat_2(X16,X21)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

fof(c_0_12,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r1_orders_2(X26,X27,X28)
        | r2_hidden(k4_tarski(X27,X28),u1_orders_2(X26))
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( ~ r2_hidden(k4_tarski(X27,X28),u1_orders_2(X26))
        | r1_orders_2(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_13,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X6,X7,X8,X9] :
      ( ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X7,X9)
        | r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X3,X5),X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X5,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X1,u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
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
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

fof(c_0_24,plain,(
    ! [X25] :
      ( ( ~ v4_orders_2(X25)
        | r8_relat_2(u1_orders_2(X25),u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( ~ r8_relat_2(u1_orders_2(X25),u1_struct_0(X25))
        | v4_orders_2(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_27,negated_conjecture,(
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

cnf(c_0_28,plain,
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
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_29,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

fof(c_0_32,negated_conjecture,
    ( v4_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & r1_orders_2(esk4_0,esk5_0,esk6_0)
    & r1_orders_2(esk4_0,esk6_0,esk7_0)
    & ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r1_orders_2(X3,X4,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(esk4_0,X2,esk7_0)
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk7_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_36]),c_0_34])])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.38  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.20/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.38  fof(d8_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r8_relat_2(X1,X2)<=>![X3, X4, X5]:(((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&r2_hidden(X5,X2))&r2_hidden(k4_tarski(X3,X4),X1))&r2_hidden(k4_tarski(X4,X5),X1))=>r2_hidden(k4_tarski(X3,X5),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_2)).
% 0.20/0.38  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.20/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.38  fof(d5_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v4_orders_2(X1)<=>r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_orders_2)).
% 0.20/0.38  fof(t26_orders_2, conjecture, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 0.20/0.38  fof(c_0_8, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.38  fof(c_0_9, plain, ![X29]:(~l1_orders_2(X29)|m1_subset_1(u1_orders_2(X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X29))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.20/0.38  fof(c_0_10, plain, ![X10, X11, X12]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|(~r2_hidden(X12,X11)|r2_hidden(X12,X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.38  fof(c_0_11, plain, ![X16, X17, X18, X19, X20, X21]:((~r8_relat_2(X16,X17)|(~r2_hidden(X18,X17)|~r2_hidden(X19,X17)|~r2_hidden(X20,X17)|~r2_hidden(k4_tarski(X18,X19),X16)|~r2_hidden(k4_tarski(X19,X20),X16)|r2_hidden(k4_tarski(X18,X20),X16))|~v1_relat_1(X16))&((((((r2_hidden(esk1_2(X16,X21),X21)|r8_relat_2(X16,X21)|~v1_relat_1(X16))&(r2_hidden(esk2_2(X16,X21),X21)|r8_relat_2(X16,X21)|~v1_relat_1(X16)))&(r2_hidden(esk3_2(X16,X21),X21)|r8_relat_2(X16,X21)|~v1_relat_1(X16)))&(r2_hidden(k4_tarski(esk1_2(X16,X21),esk2_2(X16,X21)),X16)|r8_relat_2(X16,X21)|~v1_relat_1(X16)))&(r2_hidden(k4_tarski(esk2_2(X16,X21),esk3_2(X16,X21)),X16)|r8_relat_2(X16,X21)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(esk1_2(X16,X21),esk3_2(X16,X21)),X16)|r8_relat_2(X16,X21)|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).
% 0.20/0.38  fof(c_0_12, plain, ![X26, X27, X28]:((~r1_orders_2(X26,X27,X28)|r2_hidden(k4_tarski(X27,X28),u1_orders_2(X26))|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|~l1_orders_2(X26))&(~r2_hidden(k4_tarski(X27,X28),u1_orders_2(X26))|r1_orders_2(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~m1_subset_1(X27,u1_struct_0(X26))|~l1_orders_2(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.20/0.38  cnf(c_0_13, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_15, plain, ![X6, X7, X8, X9]:(((r2_hidden(X6,X8)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))&(r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9))))&(~r2_hidden(X6,X8)|~r2_hidden(X7,X9)|r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X3,X5),X1)|~r8_relat_2(X1,X2)|~r2_hidden(X3,X2)|~r2_hidden(X4,X2)|~r2_hidden(X5,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~r2_hidden(k4_tarski(X4,X5),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_19, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))|~l1_orders_2(X2)|~r2_hidden(X1,u1_orders_2(X2))), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 0.20/0.38  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~r1_orders_2(X3,X4,X2)|~l1_orders_2(X3)|~r8_relat_2(u1_orders_2(X3),X5)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X3))|~r2_hidden(k4_tarski(X1,X4),u1_orders_2(X3))|~r2_hidden(X2,X5)|~r2_hidden(X4,X5)|~r2_hidden(X1,X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.20/0.38  fof(c_0_24, plain, ![X25]:((~v4_orders_2(X25)|r8_relat_2(u1_orders_2(X25),u1_struct_0(X25))|~l1_orders_2(X25))&(~r8_relat_2(u1_orders_2(X25),u1_struct_0(X25))|v4_orders_2(X25)|~l1_orders_2(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~r2_hidden(k4_tarski(X1,X3),u1_orders_2(X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_26, plain, (r2_hidden(X1,u1_struct_0(X2))|~l1_orders_2(X2)|~r2_hidden(k4_tarski(X3,X1),u1_orders_2(X2))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.20/0.38  fof(c_0_27, negated_conjecture, ~(![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t26_orders_2])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~r1_orders_2(X3,X4,X2)|~r1_orders_2(X3,X1,X4)|~l1_orders_2(X3)|~r8_relat_2(u1_orders_2(X3),X5)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X2,X5)|~r2_hidden(X4,X5)|~r2_hidden(X1,X5)), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.20/0.38  cnf(c_0_29, plain, (r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(X1,u1_struct_0(X2))|~r1_orders_2(X2,X1,X3)|~l1_orders_2(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.20/0.38  cnf(c_0_31, plain, (r2_hidden(X1,u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~l1_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_26, c_0_18])).
% 0.20/0.38  fof(c_0_32, negated_conjecture, ((v4_orders_2(esk4_0)&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&((r1_orders_2(esk4_0,esk5_0,esk6_0)&r1_orders_2(esk4_0,esk6_0,esk7_0))&~r1_orders_2(esk4_0,esk5_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.20/0.38  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~r1_orders_2(X3,X4,X2)|~r1_orders_2(X3,X1,X4)|~v4_orders_2(X3)|~l1_orders_2(X3)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_31])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))|~r1_orders_2(esk4_0,X2,esk7_0)|~r1_orders_2(esk4_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk4_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),u1_orders_2(esk4_0))|~r1_orders_2(esk4_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (~r1_orders_2(esk4_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk4_0,X1,esk7_0)|~r1_orders_2(esk4_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_36]), c_0_34])])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 47
% 0.20/0.38  # Proof object clause steps            : 30
% 0.20/0.38  # Proof object formula steps           : 17
% 0.20/0.38  # Proof object conjectures             : 15
% 0.20/0.38  # Proof object clause conjectures      : 12
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 17
% 0.20/0.38  # Proof object initial formulas used   : 8
% 0.20/0.38  # Proof object generating inferences   : 13
% 0.20/0.38  # Proof object simplifying inferences  : 15
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 8
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 25
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 25
% 0.20/0.38  # Processed clauses                    : 90
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 88
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 63
% 0.20/0.38  # ...of the previous two non-trivial   : 54
% 0.20/0.38  # Contextual simplify-reflections      : 5
% 0.20/0.38  # Paramodulations                      : 63
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 63
% 0.20/0.38  #    Positive orientable unit clauses  : 10
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 52
% 0.20/0.38  # Current number of unprocessed clauses: 13
% 0.20/0.38  # ...number of literals in the above   : 97
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 25
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 796
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 229
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 2
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4397
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.029 s
% 0.20/0.38  # System time              : 0.008 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

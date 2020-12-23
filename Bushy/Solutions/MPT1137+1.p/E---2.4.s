%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t25_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:18 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 226 expanded)
%              Number of clauses        :   37 (  93 expanded)
%              Number of leaves         :   10 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  224 (1021 expanded)
%              Number of equality atoms :   12 (  73 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',t106_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',t4_subset)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',dt_u1_orders_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',t5_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',cc1_relset_1)).

fof(d4_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r4_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X3),X1) )
             => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',d4_relat_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',d9_orders_2)).

fof(d6_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v5_orders_2(X1)
      <=> r4_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',d6_orders_2)).

fof(t25_orders_2,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t25_orders_2.p',t25_orders_2)).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X30] :
      ( ( r2_hidden(X27,X29)
        | ~ r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) )
      & ( r2_hidden(X28,X30)
        | ~ r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) )
      & ( ~ r2_hidden(X27,X29)
        | ~ r2_hidden(X28,X30)
        | r2_hidden(k4_tarski(X27,X28),k2_zfmisc_1(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X33,X34)
      | v1_xboole_0(X34)
      | r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_12,plain,(
    ! [X37,X38,X39] :
      ( ~ r2_hidden(X37,X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X39))
      | m1_subset_1(X37,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_13,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | m1_subset_1(u1_orders_2(X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_14,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | v1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r4_relat_2(X10,X11)
        | ~ r2_hidden(X12,X11)
        | ~ r2_hidden(X13,X11)
        | ~ r2_hidden(k4_tarski(X12,X13),X10)
        | ~ r2_hidden(k4_tarski(X13,X12),X10)
        | X12 = X13
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk4_2(X10,X14),X14)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk5_2(X10,X14),X14)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk4_2(X10,X14),esk5_2(X10,X14)),X10)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk5_2(X10,X14),esk4_2(X10,X14)),X10)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( esk4_2(X10,X14) != esk5_2(X10,X14)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_2])])])])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | r2_hidden(X3,X2)
    | ~ m1_subset_1(k4_tarski(X4,X3),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_orders_2(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r1_orders_2(X18,X19,X20)
        | r2_hidden(k4_tarski(X19,X20),u1_orders_2(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),u1_orders_2(X18))
        | r1_orders_2(X18,X19,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_27,plain,
    ( X3 = X4
    | ~ r4_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk4_2(X1,X2)),X1)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r4_relat_2(X1,X2)
    | esk4_2(X1,X2) != esk5_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),u1_orders_2(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_32,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r4_relat_2(X1,X2)
    | ~ r4_relat_2(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X3)
    | ~ r2_hidden(esk4_2(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_35,plain,
    ( r4_relat_2(u1_orders_2(X1),X2)
    | r2_hidden(esk5_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_32])).

cnf(c_0_36,plain,
    ( r4_relat_2(u1_orders_2(X1),X2)
    | r2_hidden(esk4_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_32])).

fof(c_0_37,plain,(
    ! [X17] :
      ( ( ~ v5_orders_2(X17)
        | r4_relat_2(u1_orders_2(X17),u1_struct_0(X17))
        | ~ l1_orders_2(X17) )
      & ( ~ r4_relat_2(u1_orders_2(X17),u1_struct_0(X17))
        | v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_orders_2])])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r4_relat_2(u1_orders_2(X3),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r1_orders_2(X3,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_33]),c_0_32])).

cnf(c_0_39,plain,
    ( r4_relat_2(u1_orders_2(X1),X2)
    | ~ r4_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_32])).

cnf(c_0_40,plain,
    ( r4_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ( r1_orders_2(X1,X2,X3)
                    & r1_orders_2(X1,X3,X2) )
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_orders_2])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r4_relat_2(u1_orders_2(X3),X4)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r1_orders_2(X3,X2,X1)
    | ~ r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_43,plain,
    ( r4_relat_2(u1_orders_2(X1),X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_44,negated_conjecture,
    ( v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r1_orders_2(esk1_0,esk2_0,esk3_0)
    & r1_orders_2(esk1_0,esk3_0,esk2_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X4,X2,X1)
    | ~ r1_orders_2(X4,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ l1_orders_2(X4)
    | ~ v5_orders_2(X4) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_49]),c_0_48]),c_0_50])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------

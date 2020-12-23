%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1137+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:48 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 104 expanded)
%              Number of clauses        :   27 (  43 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  196 ( 462 expanded)
%              Number of equality atoms :   12 (  30 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).

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

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(d6_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v5_orders_2(X1)
      <=> r4_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(c_0_10,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | m1_subset_1(u1_orders_2(X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X19)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_12,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,X25)
      | v1_xboole_0(X25)
      | r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r4_relat_2(X8,X9)
        | ~ r2_hidden(X10,X9)
        | ~ r2_hidden(X11,X9)
        | ~ r2_hidden(k4_tarski(X10,X11),X8)
        | ~ r2_hidden(k4_tarski(X11,X10),X8)
        | X10 = X11
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_2(X8,X12),X12)
        | r4_relat_2(X8,X12)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk2_2(X8,X12),X12)
        | r4_relat_2(X8,X12)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk1_2(X8,X12),esk2_2(X8,X12)),X8)
        | r4_relat_2(X8,X12)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk2_2(X8,X12),esk1_2(X8,X12)),X8)
        | r4_relat_2(X8,X12)
        | ~ v1_relat_1(X8) )
      & ( esk1_2(X8,X12) != esk2_2(X8,X12)
        | r4_relat_2(X8,X12)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_2])])])])])])).

fof(c_0_19,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r1_orders_2(X16,X17,X18)
        | r2_hidden(k4_tarski(X17,X18),u1_orders_2(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ l1_orders_2(X16) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),u1_orders_2(X16))
        | r1_orders_2(X16,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X20,X21,X22,X23] :
      ( ( r2_hidden(X20,X22)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) )
      & ( ~ r2_hidden(X20,X22)
        | ~ r2_hidden(X21,X23)
        | r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X1,u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,u1_orders_2(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_25,plain,
    ( X3 = X4
    | ~ r4_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X1,u1_orders_2(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_orders_2(X3,X2,X1)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r4_relat_2(u1_orders_2(X3),X4)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_31,plain,(
    ! [X15] :
      ( ( ~ v5_orders_2(X15)
        | r4_relat_2(u1_orders_2(X15),u1_struct_0(X15))
        | ~ l1_orders_2(X15) )
      & ( ~ r4_relat_2(u1_orders_2(X15),u1_struct_0(X15))
        | v5_orders_2(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_orders_2])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),u1_orders_2(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,negated_conjecture,(
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

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_orders_2(X3,X2,X1)
    | ~ r1_orders_2(X3,X1,X2)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r4_relat_2(u1_orders_2(X3),X4)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_35,plain,
    ( r4_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

fof(c_0_37,negated_conjecture,
    ( v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & r1_orders_2(esk3_0,esk4_0,esk5_0)
    & r1_orders_2(esk3_0,esk5_0,esk4_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_orders_2(X3,X2,X1)
    | ~ r1_orders_2(X3,X1,X2)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk5_0 = X1
    | ~ r1_orders_2(esk3_0,X1,esk5_0)
    | ~ r1_orders_2(esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])]),c_0_46]),
    [proof]).

%------------------------------------------------------------------------------

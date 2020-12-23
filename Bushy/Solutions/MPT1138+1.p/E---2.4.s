%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t26_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:18 EDT 2019

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 307 expanded)
%              Number of clauses        :   47 ( 126 expanded)
%              Number of leaves         :   11 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  279 (1420 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t106_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t4_subset)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',dt_u1_orders_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t5_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',d8_relat_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',d9_orders_2)).

fof(d5_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v4_orders_2(X1)
      <=> r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',d5_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t26_orders_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t26_orders_2.p',t1_subset)).

fof(c_0_11,plain,(
    ! [X31,X32,X33,X34] :
      ( ( r2_hidden(X31,X33)
        | ~ r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) )
      & ( r2_hidden(X32,X34)
        | ~ r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) )
      & ( ~ r2_hidden(X31,X33)
        | ~ r2_hidden(X32,X34)
        | r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X37,X38)
      | v1_xboole_0(X38)
      | r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_13,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | m1_subset_1(X41,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,plain,(
    ! [X26] :
      ( ~ l1_orders_2(X26)
      | m1_subset_1(u1_orders_2(X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X26)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_15,plain,(
    ! [X44,X45,X46] :
      ( ~ r2_hidden(X44,X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(X46))
      | ~ v1_xboole_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | v1_relat_1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r8_relat_2(X13,X14)
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X17,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | ~ r2_hidden(k4_tarski(X16,X17),X13)
        | r2_hidden(k4_tarski(X15,X17),X13)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk5_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk6_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk7_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk5_2(X13,X18),esk6_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk6_2(X13,X18),esk7_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X13,X18),esk7_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | r2_hidden(X3,X2)
    | ~ m1_subset_1(k4_tarski(X4,X3),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_orders_2(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X3,X5),X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ r2_hidden(X5,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk6_2(X1,X2),esk7_2(X1,X2)),X1)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),u1_orders_2(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | r2_hidden(X3,X1)
    | ~ m1_subset_1(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

fof(c_0_33,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r1_orders_2(X22,X23,X24)
        | r2_hidden(k4_tarski(X23,X24),u1_orders_2(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),u1_orders_2(X22))
        | r1_orders_2(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_34,plain,
    ( r8_relat_2(X1,X2)
    | r2_hidden(k4_tarski(X3,esk7_2(X1,X2)),X1)
    | ~ v1_relat_1(X1)
    | ~ r8_relat_2(X1,X4)
    | ~ r2_hidden(k4_tarski(X3,esk6_2(X1,X2)),X1)
    | ~ r2_hidden(esk7_2(X1,X2),X4)
    | ~ r2_hidden(esk6_2(X1,X2),X4)
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r8_relat_2(u1_orders_2(X1),X2)
    | r2_hidden(esk7_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),u1_orders_2(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_25])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r8_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),esk7_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( r8_relat_2(u1_orders_2(X1),X2)
    | r2_hidden(k4_tarski(X3,esk7_2(u1_orders_2(X1),X2)),u1_orders_2(X1))
    | ~ r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ r2_hidden(k4_tarski(X3,esk6_2(u1_orders_2(X1),X2)),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_30]),c_0_31])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_41,plain,(
    ! [X12] :
      ( ( ~ v4_orders_2(X12)
        | r8_relat_2(u1_orders_2(X12),u1_struct_0(X12))
        | ~ l1_orders_2(X12) )
      & ( ~ r8_relat_2(u1_orders_2(X12),u1_struct_0(X12))
        | v4_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r8_relat_2(u1_orders_2(X3),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),u1_orders_2(X3))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X5,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r1_orders_2(X3,X5,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_37]),c_0_31])).

cnf(c_0_43,plain,
    ( r8_relat_2(u1_orders_2(X1),X2)
    | ~ r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_31])).

cnf(c_0_44,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_45,negated_conjecture,(
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

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r8_relat_2(u1_orders_2(X3),X4)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X5,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r1_orders_2(X3,X5,X2)
    | ~ r1_orders_2(X3,X1,X5)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_47,plain,
    ( r8_relat_2(u1_orders_2(X1),X2)
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_48,negated_conjecture,
    ( v4_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & r1_orders_2(esk1_0,esk2_0,esk3_0)
    & r1_orders_2(esk1_0,esk3_0,esk4_0)
    & ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X5,X4)
    | ~ r2_hidden(X1,X4)
    | ~ r1_orders_2(X3,X5,X2)
    | ~ r1_orders_2(X3,X1,X5)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3)
    | ~ v4_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | m1_subset_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk1_0))
    | ~ r2_hidden(esk4_0,X2)
    | ~ r2_hidden(esk3_0,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_52]),c_0_57]),c_0_53])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_0),u1_orders_2(esk1_0))
    | ~ r2_hidden(X1,u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])]),c_0_62])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r2_hidden(X1,u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_51]),c_0_53])]),c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_56]),c_0_52]),c_0_57]),c_0_53])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------

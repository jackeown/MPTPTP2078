%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:21 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 633 expanded)
%              Number of clauses        :   46 ( 254 expanded)
%              Number of leaves         :   15 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  249 (2724 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t136_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( v6_orders_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => r3_orders_1(u1_orders_2(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d8_orders_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r3_orders_1(X1,X2)
        <=> ( r1_relat_2(X1,X2)
            & r8_relat_2(X1,X2)
            & r4_relat_2(X1,X2)
            & r6_relat_2(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).

fof(t92_orders_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r7_relat_2(X2,X1)
      <=> ( r1_relat_2(X2,X1)
          & r6_relat_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t94_orders_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r4_relat_2(X3,X1)
          & r1_tarski(X2,X1) )
       => r4_relat_2(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_orders_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d6_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v5_orders_2(X1)
      <=> r4_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

fof(t95_orders_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r8_relat_2(X3,X1)
          & r1_tarski(X2,X1) )
       => r8_relat_2(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_orders_1)).

fof(d5_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v4_orders_2(X1)
      <=> r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( v6_orders_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r3_orders_1(u1_orders_2(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t136_orders_2])).

fof(c_0_16,plain,(
    ! [X28] :
      ( ~ l1_orders_2(X28)
      | m1_subset_1(u1_orders_2(X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X28)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & v6_orders_2(esk3_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ~ r3_orders_1(u1_orders_2(esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ( r1_relat_2(X26,X27)
        | ~ r3_orders_1(X26,X27)
        | ~ v1_relat_1(X26) )
      & ( r8_relat_2(X26,X27)
        | ~ r3_orders_1(X26,X27)
        | ~ v1_relat_1(X26) )
      & ( r4_relat_2(X26,X27)
        | ~ r3_orders_1(X26,X27)
        | ~ v1_relat_1(X26) )
      & ( r6_relat_2(X26,X27)
        | ~ r3_orders_1(X26,X27)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_relat_2(X26,X27)
        | ~ r8_relat_2(X26,X27)
        | ~ r4_relat_2(X26,X27)
        | ~ r6_relat_2(X26,X27)
        | r3_orders_1(X26,X27)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_orders_1])])])])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( ( r1_relat_2(X30,X29)
        | ~ r7_relat_2(X30,X29)
        | ~ v1_relat_1(X30) )
      & ( r6_relat_2(X30,X29)
        | ~ r7_relat_2(X30,X29)
        | ~ v1_relat_1(X30) )
      & ( ~ r1_relat_2(X30,X29)
        | ~ r6_relat_2(X30,X29)
        | r7_relat_2(X30,X29)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_orders_1])])])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ( ~ v6_orders_2(X23,X22)
        | r7_relat_2(u1_orders_2(X22),X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( ~ r7_relat_2(u1_orders_2(X22),X23)
        | v6_orders_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | v1_relat_1(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X20,X21] : v1_relat_1(k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r4_relat_2(X33,X31)
      | ~ r1_tarski(X32,X31)
      | r4_relat_2(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_orders_1])])).

fof(c_0_26,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_27,plain,(
    ! [X25] :
      ( ( ~ v5_orders_2(X25)
        | r4_relat_2(u1_orders_2(X25),u1_struct_0(X25))
        | ~ l1_orders_2(X25) )
      & ( ~ r4_relat_2(u1_orders_2(X25),u1_struct_0(X25))
        | v5_orders_2(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_orders_2])])])).

fof(c_0_28,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ r8_relat_2(X36,X34)
      | ~ r1_tarski(X35,X34)
      | r8_relat_2(X36,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_orders_1])])).

fof(c_0_29,plain,(
    ! [X24] :
      ( ( ~ v4_orders_2(X24)
        | r8_relat_2(u1_orders_2(X24),u1_struct_0(X24))
        | ~ l1_orders_2(X24) )
      & ( ~ r8_relat_2(u1_orders_2(X24),u1_struct_0(X24))
        | v4_orders_2(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | ~ v1_xboole_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_31,plain,
    ( r3_orders_1(X1,X2)
    | ~ r1_relat_2(X1,X2)
    | ~ r8_relat_2(X1,X2)
    | ~ r4_relat_2(X1,X2)
    | ~ r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( r6_relat_2(X1,X2)
    | ~ r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( r1_relat_2(X1,X2)
    | ~ r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( r7_relat_2(u1_orders_2(X2),X1)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( v6_orders_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_39,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( r4_relat_2(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r4_relat_2(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( r4_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,plain,
    ( r8_relat_2(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r8_relat_2(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_48,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,X11)
      | v1_xboole_0(X11)
      | r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_49,plain,
    ( r3_orders_1(X1,X2)
    | ~ r4_relat_2(X1,X2)
    | ~ r8_relat_2(X1,X2)
    | ~ r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_23])])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r3_orders_1(u1_orders_2(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,plain,
    ( r4_relat_2(X1,X2)
    | r2_hidden(esk1_2(X2,X3),X2)
    | ~ r4_relat_2(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( r4_relat_2(u1_orders_2(esk2_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_23])])).

cnf(c_0_55,plain,
    ( r8_relat_2(X1,X2)
    | r2_hidden(esk1_2(X2,X3),X2)
    | ~ r8_relat_2(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r8_relat_2(u1_orders_2(esk2_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23])])).

fof(c_0_57,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( ~ r4_relat_2(u1_orders_2(esk2_0),esk3_0)
    | ~ r8_relat_2(u1_orders_2(esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r4_relat_2(u1_orders_2(esk2_0),X1)
    | r2_hidden(esk1_2(X1,u1_struct_0(esk2_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_51])])).

cnf(c_0_62,negated_conjecture,
    ( r8_relat_2(u1_orders_2(esk2_0),X1)
    | r2_hidden(esk1_2(X1,u1_struct_0(esk2_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_51])])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,u1_struct_0(esk2_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk1_2(esk3_0,u1_struct_0(esk2_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_65])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,u1_struct_0(esk2_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( r8_relat_2(X1,esk3_0)
    | ~ r8_relat_2(X1,u1_struct_0(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( r8_relat_2(u1_orders_2(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_56]),c_0_51])])).

cnf(c_0_74,negated_conjecture,
    ( r4_relat_2(X1,esk3_0)
    | ~ r4_relat_2(X1,u1_struct_0(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( ~ r4_relat_2(u1_orders_2(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_54]),c_0_51])]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01AI
% 0.12/0.37  # and selection function SelectMinOptimalNoXTypePred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t136_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:((v6_orders_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r3_orders_1(u1_orders_2(X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_orders_2)).
% 0.12/0.37  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.12/0.37  fof(d8_orders_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r3_orders_1(X1,X2)<=>(((r1_relat_2(X1,X2)&r8_relat_2(X1,X2))&r4_relat_2(X1,X2))&r6_relat_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_orders_1)).
% 0.12/0.37  fof(t92_orders_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r7_relat_2(X2,X1)<=>(r1_relat_2(X2,X1)&r6_relat_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_orders_1)).
% 0.12/0.37  fof(d11_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_orders_2(X2,X1)<=>r7_relat_2(u1_orders_2(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_orders_2)).
% 0.12/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.37  fof(t94_orders_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r4_relat_2(X3,X1)&r1_tarski(X2,X1))=>r4_relat_2(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_orders_1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(d6_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v5_orders_2(X1)<=>r4_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_orders_2)).
% 0.12/0.37  fof(t95_orders_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r8_relat_2(X3,X1)&r1_tarski(X2,X1))=>r8_relat_2(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_orders_1)).
% 0.12/0.37  fof(d5_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v4_orders_2(X1)<=>r8_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 0.12/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.12/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.37  fof(c_0_15, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:((v6_orders_2(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r3_orders_1(u1_orders_2(X1),X2)))), inference(assume_negation,[status(cth)],[t136_orders_2])).
% 0.12/0.37  fof(c_0_16, plain, ![X28]:(~l1_orders_2(X28)|m1_subset_1(u1_orders_2(X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X28))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&((v6_orders_2(esk3_0,esk2_0)&m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))))&~r3_orders_1(u1_orders_2(esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.12/0.37  fof(c_0_18, plain, ![X26, X27]:(((((r1_relat_2(X26,X27)|~r3_orders_1(X26,X27)|~v1_relat_1(X26))&(r8_relat_2(X26,X27)|~r3_orders_1(X26,X27)|~v1_relat_1(X26)))&(r4_relat_2(X26,X27)|~r3_orders_1(X26,X27)|~v1_relat_1(X26)))&(r6_relat_2(X26,X27)|~r3_orders_1(X26,X27)|~v1_relat_1(X26)))&(~r1_relat_2(X26,X27)|~r8_relat_2(X26,X27)|~r4_relat_2(X26,X27)|~r6_relat_2(X26,X27)|r3_orders_1(X26,X27)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_orders_1])])])])).
% 0.12/0.37  fof(c_0_19, plain, ![X29, X30]:(((r1_relat_2(X30,X29)|~r7_relat_2(X30,X29)|~v1_relat_1(X30))&(r6_relat_2(X30,X29)|~r7_relat_2(X30,X29)|~v1_relat_1(X30)))&(~r1_relat_2(X30,X29)|~r6_relat_2(X30,X29)|r7_relat_2(X30,X29)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_orders_1])])])).
% 0.12/0.37  fof(c_0_20, plain, ![X22, X23]:((~v6_orders_2(X23,X22)|r7_relat_2(u1_orders_2(X22),X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_orders_2(X22))&(~r7_relat_2(u1_orders_2(X22),X23)|v6_orders_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_orders_2(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).
% 0.12/0.37  fof(c_0_21, plain, ![X18, X19]:(~v1_relat_1(X18)|(~m1_subset_1(X19,k1_zfmisc_1(X18))|v1_relat_1(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.37  cnf(c_0_22, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_24, plain, ![X20, X21]:v1_relat_1(k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.37  fof(c_0_25, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|(~r4_relat_2(X33,X31)|~r1_tarski(X32,X31)|r4_relat_2(X33,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_orders_1])])).
% 0.12/0.37  fof(c_0_26, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  fof(c_0_27, plain, ![X25]:((~v5_orders_2(X25)|r4_relat_2(u1_orders_2(X25),u1_struct_0(X25))|~l1_orders_2(X25))&(~r4_relat_2(u1_orders_2(X25),u1_struct_0(X25))|v5_orders_2(X25)|~l1_orders_2(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_orders_2])])])).
% 0.12/0.37  fof(c_0_28, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|(~r8_relat_2(X36,X34)|~r1_tarski(X35,X34)|r8_relat_2(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_orders_1])])).
% 0.12/0.37  fof(c_0_29, plain, ![X24]:((~v4_orders_2(X24)|r8_relat_2(u1_orders_2(X24),u1_struct_0(X24))|~l1_orders_2(X24))&(~r8_relat_2(u1_orders_2(X24),u1_struct_0(X24))|v4_orders_2(X24)|~l1_orders_2(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_2])])])).
% 0.12/0.37  fof(c_0_30, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|~v1_xboole_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.12/0.37  cnf(c_0_31, plain, (r3_orders_1(X1,X2)|~r1_relat_2(X1,X2)|~r8_relat_2(X1,X2)|~r4_relat_2(X1,X2)|~r6_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_32, plain, (r6_relat_2(X1,X2)|~r7_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_33, plain, (r1_relat_2(X1,X2)|~r7_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_34, plain, (r7_relat_2(u1_orders_2(X2),X1)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (v6_orders_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_37, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.37  cnf(c_0_39, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_40, plain, (r4_relat_2(X1,X3)|~v1_relat_1(X1)|~r4_relat_2(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_42, plain, (r4_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_44, plain, (r8_relat_2(X1,X3)|~v1_relat_1(X1)|~r8_relat_2(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_45, plain, (r8_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v4_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  fof(c_0_48, plain, ![X10, X11]:(~m1_subset_1(X10,X11)|(v1_xboole_0(X11)|r2_hidden(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.37  cnf(c_0_49, plain, (r3_orders_1(X1,X2)|~r4_relat_2(X1,X2)|~r8_relat_2(X1,X2)|~r7_relat_2(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (r7_relat_2(u1_orders_2(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_23])])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (v1_relat_1(u1_orders_2(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (~r3_orders_1(u1_orders_2(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_53, plain, (r4_relat_2(X1,X2)|r2_hidden(esk1_2(X2,X3),X2)|~r4_relat_2(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (r4_relat_2(u1_orders_2(esk2_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_23])])).
% 0.12/0.37  cnf(c_0_55, plain, (r8_relat_2(X1,X2)|r2_hidden(esk1_2(X2,X3),X2)|~r8_relat_2(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_41])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (r8_relat_2(u1_orders_2(esk2_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_23])])).
% 0.12/0.37  fof(c_0_57, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|m1_subset_1(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_35])).
% 0.12/0.37  cnf(c_0_59, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (~r4_relat_2(u1_orders_2(esk2_0),esk3_0)|~r8_relat_2(u1_orders_2(esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), c_0_52])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (r4_relat_2(u1_orders_2(esk2_0),X1)|r2_hidden(esk1_2(X1,u1_struct_0(esk2_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_51])])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (r8_relat_2(u1_orders_2(esk2_0),X1)|r2_hidden(esk1_2(X1,u1_struct_0(esk2_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_51])])).
% 0.12/0.37  cnf(c_0_63, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X2,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_2(esk3_0,u1_struct_0(esk2_0)),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_35])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk1_2(esk3_0,u1_struct_0(esk2_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_65])).
% 0.12/0.37  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_2(esk3_0,u1_struct_0(esk2_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, (r8_relat_2(X1,esk3_0)|~r8_relat_2(X1,u1_struct_0(esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_71])).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (r8_relat_2(u1_orders_2(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_56]), c_0_51])])).
% 0.12/0.37  cnf(c_0_74, negated_conjecture, (r4_relat_2(X1,esk3_0)|~r4_relat_2(X1,u1_struct_0(esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_71])).
% 0.12/0.37  cnf(c_0_75, negated_conjecture, (~r4_relat_2(u1_orders_2(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_73])])).
% 0.12/0.37  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_54]), c_0_51])]), c_0_75]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 77
% 0.12/0.38  # Proof object clause steps            : 46
% 0.12/0.38  # Proof object formula steps           : 31
% 0.12/0.38  # Proof object conjectures             : 30
% 0.12/0.38  # Proof object clause conjectures      : 27
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 22
% 0.12/0.38  # Proof object initial formulas used   : 15
% 0.12/0.38  # Proof object generating inferences   : 23
% 0.12/0.38  # Proof object simplifying inferences  : 25
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 15
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 33
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 33
% 0.12/0.38  # Processed clauses                    : 120
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 10
% 0.12/0.38  # ...remaining for further processing  : 109
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 2
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 110
% 0.12/0.38  # ...of the previous two non-trivial   : 94
% 0.12/0.38  # Contextual simplify-reflections      : 3
% 0.12/0.38  # Paramodulations                      : 110
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 72
% 0.12/0.38  #    Positive orientable unit clauses  : 17
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 52
% 0.12/0.38  # Current number of unprocessed clauses: 39
% 0.12/0.38  # ...number of literals in the above   : 148
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 37
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 492
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 294
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.12/0.38  # Unit Clause-clause subsumption calls : 32
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 4461
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.032 s
% 0.12/0.38  # System time              : 0.005 s
% 0.12/0.38  # Total time               : 0.037 s
% 0.12/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

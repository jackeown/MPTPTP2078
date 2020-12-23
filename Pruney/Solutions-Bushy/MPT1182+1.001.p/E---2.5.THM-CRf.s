%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1182+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:52 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 323 expanded)
%              Number of clauses        :   57 ( 133 expanded)
%              Number of leaves         :   16 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  401 (1697 expanded)
%              Number of equality atoms :   28 (  39 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d7_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r7_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ~ ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & ~ r2_hidden(k4_tarski(X3,X4),X1)
                & ~ r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_2)).

fof(t108_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_orders_1(k2_wellord1(u1_orders_2(X1),X2))
           => ( v6_orders_2(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_orders_2)).

fof(t107_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k3_relat_1(k2_wellord1(u1_orders_2(X1),X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_orders_2)).

fof(d6_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r6_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ~ ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & X3 != X4
                & ~ r2_hidden(k4_tarski(X3,X4),X1)
                & ~ r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_2)).

fof(d14_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> r6_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

fof(d5_orders_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v3_orders_1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(c_0_16,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,plain,(
    ! [X42] :
      ( ~ l1_orders_2(X42)
      | m1_subset_1(u1_orders_2(X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X42)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_18,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( ~ r7_relat_2(X30,X31)
        | ~ r2_hidden(X32,X31)
        | ~ r2_hidden(X33,X31)
        | r2_hidden(k4_tarski(X32,X33),X30)
        | r2_hidden(k4_tarski(X33,X32),X30)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk4_2(X30,X34),X34)
        | r7_relat_2(X30,X34)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk5_2(X30,X34),X34)
        | r7_relat_2(X30,X34)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X30,X34),esk5_2(X30,X34)),X30)
        | r7_relat_2(X30,X34)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X30,X34),esk4_2(X30,X34)),X30)
        | r7_relat_2(X30,X34)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_orders_1(k2_wellord1(u1_orders_2(X1),X2))
             => ( v6_orders_2(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t108_orders_2])).

cnf(c_0_22,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & v5_orders_2(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & v3_orders_1(k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    & ( ~ v6_orders_2(esk7_0,esk6_0)
      | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_25,plain,(
    ! [X49,X50] :
      ( v2_struct_0(X49)
      | ~ v3_orders_2(X49)
      | ~ v4_orders_2(X49)
      | ~ v5_orders_2(X49)
      | ~ l1_orders_2(X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
      | k3_relat_1(k2_wellord1(u1_orders_2(X49),X50)) = X50 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t107_orders_2])])])])).

fof(c_0_26,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r6_relat_2(X21,X22)
        | ~ r2_hidden(X23,X22)
        | ~ r2_hidden(X24,X22)
        | X23 = X24
        | r2_hidden(k4_tarski(X23,X24),X21)
        | r2_hidden(k4_tarski(X24,X23),X21)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk2_2(X21,X25),X25)
        | r6_relat_2(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk3_2(X21,X25),X25)
        | r6_relat_2(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( esk2_2(X21,X25) != esk3_2(X21,X25)
        | r6_relat_2(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X21,X25),esk3_2(X21,X25)),X21)
        | r6_relat_2(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X21,X25),esk2_2(X21,X25)),X21)
        | r6_relat_2(X21,X25)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_relat_2])])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_2(u1_orders_2(X1),X2),X2)
    | r7_relat_2(u1_orders_2(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X10] :
      ( ( ~ v6_relat_2(X10)
        | r6_relat_2(X10,k3_relat_1(X10))
        | ~ v1_relat_1(X10) )
      & ( ~ r6_relat_2(X10,k3_relat_1(X10))
        | v6_relat_2(X10)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_2])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k3_relat_1(k2_wellord1(u1_orders_2(X1),X2)) = X2
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( X3 = X4
    | r2_hidden(k4_tarski(X3,X4),X1)
    | r2_hidden(k4_tarski(X4,X3),X1)
    | ~ r6_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_2(u1_orders_2(esk6_0),X1),X1)
    | r7_relat_2(u1_orders_2(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( r2_hidden(esk5_2(u1_orders_2(X1),X2),X2)
    | r7_relat_2(u1_orders_2(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_40,plain,
    ( r6_relat_2(X1,k3_relat_1(X1))
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( k3_relat_1(k2_wellord1(u1_orders_2(esk6_0),esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_28])]),c_0_36])).

fof(c_0_42,plain,(
    ! [X20] :
      ( ( v1_relat_2(X20)
        | ~ v3_orders_1(X20)
        | ~ v1_relat_1(X20) )
      & ( v8_relat_2(X20)
        | ~ v3_orders_1(X20)
        | ~ v1_relat_1(X20) )
      & ( v4_relat_2(X20)
        | ~ v3_orders_1(X20)
        | ~ v1_relat_1(X20) )
      & ( v6_relat_2(X20)
        | ~ v3_orders_1(X20)
        | ~ v1_relat_1(X20) )
      & ( ~ v1_relat_2(X20)
        | ~ v8_relat_2(X20)
        | ~ v4_relat_2(X20)
        | ~ v6_relat_2(X20)
        | v3_orders_1(X20)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_orders_1])])])).

cnf(c_0_43,negated_conjecture,
    ( X1 = esk4_2(u1_orders_2(esk6_0),X2)
    | r2_hidden(k4_tarski(esk4_2(u1_orders_2(esk6_0),X2),X1),X3)
    | r2_hidden(k4_tarski(X1,esk4_2(u1_orders_2(esk6_0),X2)),X3)
    | r7_relat_2(u1_orders_2(esk6_0),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r6_relat_2(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_2(u1_orders_2(esk6_0),X1),X1)
    | r7_relat_2(u1_orders_2(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( r6_relat_2(k2_wellord1(u1_orders_2(esk6_0),esk7_0),esk7_0)
    | ~ v6_relat_2(k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | ~ v1_relat_1(k2_wellord1(u1_orders_2(esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( v6_relat_2(X1)
    | ~ v3_orders_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v3_orders_1(k2_wellord1(u1_orders_2(esk6_0),esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_48,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X16)
        | r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X17)
        | r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),X1) = esk4_2(u1_orders_2(esk6_0),X1)
    | r2_hidden(k4_tarski(esk5_2(u1_orders_2(esk6_0),X1),esk4_2(u1_orders_2(esk6_0),X1)),X2)
    | r2_hidden(k4_tarski(esk4_2(u1_orders_2(esk6_0),X1),esk5_2(u1_orders_2(esk6_0),X1)),X2)
    | r7_relat_2(u1_orders_2(esk6_0),X1)
    | ~ r6_relat_2(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r6_relat_2(k2_wellord1(u1_orders_2(esk6_0),esk7_0),esk7_0)
    | ~ v1_relat_1(k2_wellord1(u1_orders_2(esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

fof(c_0_51,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X40)
      | v1_relat_1(k2_wellord1(X40,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_52,plain,(
    ! [X51,X52,X53] :
      ( ~ r2_hidden(X51,X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(X53))
      | m1_subset_1(X51,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | k2_wellord1(X28,X29) = k3_xboole_0(X28,k2_zfmisc_1(X29,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

cnf(c_0_55,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),esk7_0) = esk4_2(u1_orders_2(esk6_0),esk7_0)
    | r2_hidden(k4_tarski(esk4_2(u1_orders_2(esk6_0),esk7_0),esk5_2(u1_orders_2(esk6_0),esk7_0)),k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | r2_hidden(k4_tarski(esk5_2(u1_orders_2(esk6_0),esk7_0),esk4_2(u1_orders_2(esk6_0),esk7_0)),k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0)
    | ~ v1_relat_1(k2_wellord1(u1_orders_2(esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_57,plain,(
    ! [X46,X47,X48] :
      ( v2_struct_0(X46)
      | ~ v3_orders_2(X46)
      | ~ l1_orders_2(X46)
      | ~ m1_subset_1(X47,u1_struct_0(X46))
      | ~ m1_subset_1(X48,u1_struct_0(X46))
      | r3_orders_2(X46,X47,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),esk7_0) = esk4_2(u1_orders_2(esk6_0),esk7_0)
    | r2_hidden(k4_tarski(esk5_2(u1_orders_2(esk6_0),esk7_0),esk4_2(u1_orders_2(esk6_0),esk7_0)),k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | r2_hidden(k4_tarski(esk4_2(u1_orders_2(esk6_0),esk7_0),esk5_2(u1_orders_2(esk6_0),esk7_0)),k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0)
    | ~ v1_relat_1(u1_orders_2(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_32])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_wellord1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),esk7_0) = esk4_2(u1_orders_2(esk6_0),esk7_0)
    | r2_hidden(k4_tarski(esk4_2(u1_orders_2(esk6_0),esk7_0),esk5_2(u1_orders_2(esk6_0),esk7_0)),k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | r2_hidden(k4_tarski(esk5_2(u1_orders_2(esk6_0),esk7_0),esk4_2(u1_orders_2(esk6_0),esk7_0)),k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_23]),c_0_28])])).

cnf(c_0_66,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),esk4_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( r3_orders_2(esk6_0,X1,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_35]),c_0_28])]),c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),esk7_0) = esk4_2(u1_orders_2(esk6_0),esk7_0)
    | r2_hidden(k4_tarski(esk4_2(u1_orders_2(esk6_0),esk7_0),esk5_2(u1_orders_2(esk6_0),esk7_0)),k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0)
    | ~ v1_relat_1(u1_orders_2(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

fof(c_0_69,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r3_orders_2(X43,X44,X45)
        | r1_orders_2(X43,X44,X45)
        | v2_struct_0(X43)
        | ~ v3_orders_2(X43)
        | ~ l1_orders_2(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43)) )
      & ( ~ r1_orders_2(X43,X44,X45)
        | r3_orders_2(X43,X44,X45)
        | v2_struct_0(X43)
        | ~ v3_orders_2(X43)
        | ~ l1_orders_2(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_70,negated_conjecture,
    ( r3_orders_2(esk6_0,X1,X1)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

fof(c_0_71,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r1_orders_2(X37,X38,X39)
        | r2_hidden(k4_tarski(X38,X39),u1_orders_2(X37))
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ l1_orders_2(X37) )
      & ( ~ r2_hidden(k4_tarski(X38,X39),u1_orders_2(X37))
        | r1_orders_2(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ l1_orders_2(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_72,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),esk7_0) = esk4_2(u1_orders_2(esk6_0),esk7_0)
    | r2_hidden(k4_tarski(esk4_2(u1_orders_2(esk6_0),esk7_0),esk5_2(u1_orders_2(esk6_0),esk7_0)),k2_wellord1(u1_orders_2(esk6_0),esk7_0))
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_23]),c_0_28])])).

cnf(c_0_73,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_74,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( r3_orders_2(esk6_0,X1,X1)
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_38])).

cnf(c_0_76,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),esk7_0) = esk4_2(u1_orders_2(esk6_0),esk7_0)
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0)
    | ~ v1_relat_1(u1_orders_2(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_72]),c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r1_orders_2(esk6_0,X1,X2)
    | ~ r3_orders_2(esk6_0,X1,X2)
    | ~ r2_hidden(X2,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_63]),c_0_35]),c_0_28])]),c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( r3_orders_2(esk6_0,esk4_2(u1_orders_2(esk6_0),esk7_0),esk4_2(u1_orders_2(esk6_0),esk7_0))
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_38])).

cnf(c_0_80,plain,
    ( r7_relat_2(u1_orders_2(X1),X2)
    | ~ r1_orders_2(X1,esk5_2(u1_orders_2(X1),X2),esk4_2(u1_orders_2(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk4_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ m1_subset_1(esk5_2(u1_orders_2(X1),X2),u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_76]),c_0_23])).

cnf(c_0_81,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),esk7_0) = esk4_2(u1_orders_2(esk6_0),esk7_0)
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_23]),c_0_28])])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk6_0,esk4_2(u1_orders_2(esk6_0),esk7_0),esk4_2(u1_orders_2(esk6_0),esk7_0))
    | r7_relat_2(u1_orders_2(esk6_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_63]),c_0_38])).

fof(c_0_83,plain,(
    ! [X8,X9] :
      ( ( ~ v6_orders_2(X9,X8)
        | r7_relat_2(u1_orders_2(X8),X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_orders_2(X8) )
      & ( ~ r7_relat_2(u1_orders_2(X8),X9)
        | v6_orders_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_84,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk6_0),esk7_0)
    | ~ m1_subset_1(esk4_2(u1_orders_2(esk6_0),esk7_0),u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_28])]),c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( ~ v6_orders_2(esk7_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_86,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk6_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_63]),c_0_38])).

cnf(c_0_88,negated_conjecture,
    ( ~ v6_orders_2(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_32])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_28]),c_0_32])]),c_0_88]),
    [proof]).

%------------------------------------------------------------------------------

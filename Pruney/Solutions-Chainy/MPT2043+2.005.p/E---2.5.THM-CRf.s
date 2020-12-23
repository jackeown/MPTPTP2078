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
% DateTime   : Thu Dec  3 11:21:49 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 232 expanded)
%              Number of clauses        :   50 ( 108 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  210 ( 733 expanded)
%              Number of equality atoms :   36 ( 154 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_yellow19,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
            & v2_waybel_0(X2,k3_yellow_1(X1))
            & v13_waybel_0(X2,k3_yellow_1(X1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
         => ! [X3] :
              ~ ( r2_hidden(X3,X2)
                & v1_xboole_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

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

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t11_waybel_7,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
     => ( v13_waybel_0(X2,k3_yellow_1(X1))
      <=> ! [X3,X4] :
            ( ( r1_tarski(X3,X4)
              & r1_tarski(X4,X1)
              & r2_hidden(X3,X2) )
           => r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
              & v2_waybel_0(X2,k3_yellow_1(X1))
              & v13_waybel_0(X2,k3_yellow_1(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
           => ! [X3] :
                ~ ( r2_hidden(X3,X2)
                  & v1_xboole_0(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_yellow19])).

fof(c_0_12,plain,(
    ! [X32] : k3_yellow_1(X32) = k2_yellow_1(k9_setfam_1(X32)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_13,plain,(
    ! [X30] : k9_setfam_1(X30) = k1_zfmisc_1(X30) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_14,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0)
    & ~ v1_xboole_0(esk9_0)
    & v1_subset_1(esk9_0,u1_struct_0(k3_yellow_1(esk8_0)))
    & v2_waybel_0(esk9_0,k3_yellow_1(esk8_0))
    & v13_waybel_0(esk9_0,k3_yellow_1(esk8_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk8_0))))
    & r2_hidden(esk10_0,esk9_0)
    & v1_xboole_0(esk10_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_16,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X18,X17)
        | r1_tarski(X18,X16)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r1_tarski(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X21)
        | ~ r1_tarski(esk3_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) )
      & ( r2_hidden(esk3_2(X20,X21),X21)
        | r1_tarski(esk3_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X31] :
      ( u1_struct_0(k2_yellow_1(X31)) = X31
      & u1_orders_2(k2_yellow_1(X31)) = k1_yellow_1(X31) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,X29)
      | v1_xboole_0(X29)
      | r2_hidden(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk8_0))))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k1_zfmisc_1(esk8_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_30])).

fof(c_0_35,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ v13_waybel_0(X36,k3_yellow_1(X35))
        | ~ r1_tarski(X37,X38)
        | ~ r1_tarski(X38,X35)
        | ~ r2_hidden(X37,X36)
        | r2_hidden(X38,X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35)))) )
      & ( r1_tarski(esk6_2(X35,X36),esk7_2(X35,X36))
        | v13_waybel_0(X36,k3_yellow_1(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35)))) )
      & ( r1_tarski(esk7_2(X35,X36),X35)
        | v13_waybel_0(X36,k3_yellow_1(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35)))) )
      & ( r2_hidden(esk6_2(X35,X36),X36)
        | v13_waybel_0(X36,k3_yellow_1(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35)))) )
      & ( ~ r2_hidden(esk7_2(X35,X36),X36)
        | v13_waybel_0(X36,k3_yellow_1(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk9_0,k1_zfmisc_1(k1_zfmisc_1(esk8_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(esk8_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,k3_yellow_1(X2))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk9_0,k1_zfmisc_1(k1_zfmisc_1(esk8_0))) ),
    inference(sr,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(X4,X1)
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ v13_waybel_0(X1,k2_yellow_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_22]),c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( v13_waybel_0(esk9_0,k3_yellow_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | k1_zfmisc_1(k1_zfmisc_1(esk8_0)) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,k2_yellow_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X4,X1)
    | ~ r2_hidden(X4,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( v13_waybel_0(esk9_0,k2_yellow_1(k1_zfmisc_1(esk8_0))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,X2)
    | k1_zfmisc_1(k1_zfmisc_1(esk8_0)) != k1_zfmisc_1(X2)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r1_tarski(X1,esk8_0)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X2,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_32])])).

cnf(c_0_49,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_tarski(esk3_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk8_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k1_zfmisc_1(esk8_0)
    | r2_hidden(esk3_2(esk8_0,X1),esk9_0)
    | r2_hidden(esk3_2(esk8_0,X1),X1)
    | ~ r1_tarski(X2,esk3_2(esk8_0,X1))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_56,plain,(
    ! [X26] :
      ( m1_subset_1(esk5_1(X26),k1_zfmisc_1(X26))
      & ~ v1_subset_1(esk5_1(X26),X26) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

fof(c_0_57,plain,(
    ! [X33,X34] :
      ( ( ~ v1_subset_1(X34,X33)
        | X34 != X33
        | ~ m1_subset_1(X34,k1_zfmisc_1(X33)) )
      & ( X34 = X33
        | v1_subset_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_58,negated_conjecture,
    ( v1_subset_1(esk9_0,u1_struct_0(k3_yellow_1(esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r1_tarski(esk3_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(esk8_0) != k1_zfmisc_1(X2)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k1_zfmisc_1(esk8_0)
    | r2_hidden(esk3_2(esk8_0,X1),esk9_0)
    | r2_hidden(esk3_2(esk8_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_62,plain,
    ( ~ v1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( v1_subset_1(esk9_0,u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk8_0)))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( X1 = k1_zfmisc_1(X2)
    | k1_zfmisc_1(esk8_0) != k1_zfmisc_1(X2)
    | ~ r2_hidden(esk3_2(X2,X1),esk9_0)
    | ~ r2_hidden(esk3_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k1_zfmisc_1(esk8_0) = esk9_0
    | r2_hidden(esk3_2(esk8_0,esk9_0),esk9_0) ),
    inference(ef,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( esk5_1(X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_69,negated_conjecture,
    ( v1_subset_1(esk9_0,k1_zfmisc_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_28])).

cnf(c_0_70,negated_conjecture,
    ( k1_zfmisc_1(esk8_0) = esk9_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_67])).

cnf(c_0_71,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_62,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S0Y
% 0.19/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.030 s
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t2_yellow19, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 0.19/0.46  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.19/0.46  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.19/0.46  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.46  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.46  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.19/0.46  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.46  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.46  fof(t11_waybel_7, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))=>(v13_waybel_0(X2,k3_yellow_1(X1))<=>![X3, X4]:(((r1_tarski(X3,X4)&r1_tarski(X4,X1))&r2_hidden(X3,X2))=>r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_waybel_7)).
% 0.19/0.46  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.19/0.46  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.46  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))))&v2_waybel_0(X2,k3_yellow_1(X1)))&v13_waybel_0(X2,k3_yellow_1(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))))=>![X3]:~((r2_hidden(X3,X2)&v1_xboole_0(X3)))))), inference(assume_negation,[status(cth)],[t2_yellow19])).
% 0.19/0.46  fof(c_0_12, plain, ![X32]:k3_yellow_1(X32)=k2_yellow_1(k9_setfam_1(X32)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.19/0.46  fof(c_0_13, plain, ![X30]:k9_setfam_1(X30)=k1_zfmisc_1(X30), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.19/0.46  fof(c_0_14, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.46  fof(c_0_15, negated_conjecture, (~v1_xboole_0(esk8_0)&(((((~v1_xboole_0(esk9_0)&v1_subset_1(esk9_0,u1_struct_0(k3_yellow_1(esk8_0))))&v2_waybel_0(esk9_0,k3_yellow_1(esk8_0)))&v13_waybel_0(esk9_0,k3_yellow_1(esk8_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk8_0)))))&(r2_hidden(esk10_0,esk9_0)&v1_xboole_0(esk10_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.46  cnf(c_0_16, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_17, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  fof(c_0_18, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X18,X17)|r1_tarski(X18,X16)|X17!=k1_zfmisc_1(X16))&(~r1_tarski(X19,X16)|r2_hidden(X19,X17)|X17!=k1_zfmisc_1(X16)))&((~r2_hidden(esk3_2(X20,X21),X21)|~r1_tarski(esk3_2(X20,X21),X20)|X21=k1_zfmisc_1(X20))&(r2_hidden(esk3_2(X20,X21),X21)|r1_tarski(esk3_2(X20,X21),X20)|X21=k1_zfmisc_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.46  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_20, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_22, plain, (k3_yellow_1(X1)=k2_yellow_1(k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.46  fof(c_0_23, plain, ![X31]:(u1_struct_0(k2_yellow_1(X31))=X31&u1_orders_2(k2_yellow_1(X31))=k1_yellow_1(X31)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.19/0.46  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.46  fof(c_0_26, plain, ![X28, X29]:(~m1_subset_1(X28,X29)|(v1_xboole_0(X29)|r2_hidden(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.46  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk8_0)))))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.46  cnf(c_0_28, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.46  fof(c_0_29, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.46  cnf(c_0_30, plain, (r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.46  cnf(c_0_31, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.46  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k1_zfmisc_1(esk8_0)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.46  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.46  cnf(c_0_34, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.46  fof(c_0_35, plain, ![X35, X36, X37, X38]:((~v13_waybel_0(X36,k3_yellow_1(X35))|(~r1_tarski(X37,X38)|~r1_tarski(X38,X35)|~r2_hidden(X37,X36)|r2_hidden(X38,X36))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35)))))&((((r1_tarski(esk6_2(X35,X36),esk7_2(X35,X36))|v13_waybel_0(X36,k3_yellow_1(X35))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35)))))&(r1_tarski(esk7_2(X35,X36),X35)|v13_waybel_0(X36,k3_yellow_1(X35))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35))))))&(r2_hidden(esk6_2(X35,X36),X36)|v13_waybel_0(X36,k3_yellow_1(X35))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35))))))&(~r2_hidden(esk7_2(X35,X36),X36)|v13_waybel_0(X36,k3_yellow_1(X35))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X35))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_waybel_7])])])])])).
% 0.19/0.46  cnf(c_0_36, negated_conjecture, (r2_hidden(esk9_0,k1_zfmisc_1(k1_zfmisc_1(esk8_0)))|v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(esk8_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.46  cnf(c_0_37, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.46  cnf(c_0_38, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,k3_yellow_1(X2))|~r1_tarski(X3,X4)|~r1_tarski(X4,X2)|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.46  cnf(c_0_39, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_40, negated_conjecture, (r2_hidden(esk9_0,k1_zfmisc_1(k1_zfmisc_1(esk8_0)))), inference(sr,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.46  cnf(c_0_41, plain, (r2_hidden(X4,X1)|~r2_hidden(X3,X1)|~r1_tarski(X4,X2)|~r1_tarski(X3,X4)|~v13_waybel_0(X1,k2_yellow_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(k1_zfmisc_1(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_22]), c_0_22])).
% 0.19/0.46  cnf(c_0_42, negated_conjecture, (v13_waybel_0(esk9_0,k3_yellow_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_43, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_44, negated_conjecture, (r1_tarski(esk9_0,X1)|k1_zfmisc_1(k1_zfmisc_1(esk8_0))!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.46  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,k2_yellow_1(k1_zfmisc_1(X3)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~r1_tarski(X1,X3)|~r1_tarski(X4,X1)|~r2_hidden(X4,X2)), inference(rw,[status(thm)],[c_0_41, c_0_28])).
% 0.19/0.46  cnf(c_0_46, negated_conjecture, (v13_waybel_0(esk9_0,k2_yellow_1(k1_zfmisc_1(esk8_0)))), inference(rw,[status(thm)],[c_0_42, c_0_22])).
% 0.19/0.46  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,X2)|k1_zfmisc_1(k1_zfmisc_1(esk8_0))!=k1_zfmisc_1(X2)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.46  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,esk9_0)|~r1_tarski(X1,esk8_0)|~r1_tarski(X2,X1)|~r2_hidden(X2,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_32])])).
% 0.19/0.46  cnf(c_0_49, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_tarski(esk3_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_20])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (v1_xboole_0(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk8_0))|~r2_hidden(X1,esk9_0)), inference(er,[status(thm)],[c_0_47])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (X1=k1_zfmisc_1(esk8_0)|r2_hidden(esk3_2(esk8_0,X1),esk9_0)|r2_hidden(esk3_2(esk8_0,X1),X1)|~r1_tarski(X2,esk3_2(esk8_0,X1))|~r2_hidden(X2,esk9_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (r1_tarski(esk10_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.46  cnf(c_0_55, negated_conjecture, (r2_hidden(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  fof(c_0_56, plain, ![X26]:(m1_subset_1(esk5_1(X26),k1_zfmisc_1(X26))&~v1_subset_1(esk5_1(X26),X26)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.19/0.46  fof(c_0_57, plain, ![X33, X34]:((~v1_subset_1(X34,X33)|X34!=X33|~m1_subset_1(X34,k1_zfmisc_1(X33)))&(X34=X33|v1_subset_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.46  cnf(c_0_58, negated_conjecture, (v1_subset_1(esk9_0,u1_struct_0(k3_yellow_1(esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_59, plain, (X2=k1_zfmisc_1(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r1_tarski(esk3_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_60, negated_conjecture, (r1_tarski(X1,X2)|k1_zfmisc_1(esk8_0)!=k1_zfmisc_1(X2)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_39, c_0_52])).
% 0.19/0.46  cnf(c_0_61, negated_conjecture, (X1=k1_zfmisc_1(esk8_0)|r2_hidden(esk3_2(esk8_0,X1),esk9_0)|r2_hidden(esk3_2(esk8_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.19/0.46  cnf(c_0_62, plain, (~v1_subset_1(esk5_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.46  cnf(c_0_63, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.46  cnf(c_0_64, plain, (m1_subset_1(esk5_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.46  cnf(c_0_65, negated_conjecture, (v1_subset_1(esk9_0,u1_struct_0(k2_yellow_1(k1_zfmisc_1(esk8_0))))), inference(rw,[status(thm)],[c_0_58, c_0_22])).
% 0.19/0.46  cnf(c_0_66, negated_conjecture, (X1=k1_zfmisc_1(X2)|k1_zfmisc_1(esk8_0)!=k1_zfmisc_1(X2)|~r2_hidden(esk3_2(X2,X1),esk9_0)|~r2_hidden(esk3_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.46  cnf(c_0_67, negated_conjecture, (k1_zfmisc_1(esk8_0)=esk9_0|r2_hidden(esk3_2(esk8_0,esk9_0),esk9_0)), inference(ef,[status(thm)],[c_0_61])).
% 0.19/0.46  cnf(c_0_68, plain, (esk5_1(X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.19/0.46  cnf(c_0_69, negated_conjecture, (v1_subset_1(esk9_0,k1_zfmisc_1(esk8_0))), inference(rw,[status(thm)],[c_0_65, c_0_28])).
% 0.19/0.46  cnf(c_0_70, negated_conjecture, (k1_zfmisc_1(esk8_0)=esk9_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_67])).
% 0.19/0.46  cnf(c_0_71, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_62, c_0_68])).
% 0.19/0.46  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_71]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 73
% 0.19/0.46  # Proof object clause steps            : 50
% 0.19/0.46  # Proof object formula steps           : 23
% 0.19/0.46  # Proof object conjectures             : 27
% 0.19/0.46  # Proof object clause conjectures      : 24
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 21
% 0.19/0.46  # Proof object initial formulas used   : 11
% 0.19/0.46  # Proof object generating inferences   : 18
% 0.19/0.46  # Proof object simplifying inferences  : 20
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 13
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 34
% 0.19/0.46  # Removed in clause preprocessing      : 3
% 0.19/0.46  # Initial clauses in saturation        : 31
% 0.19/0.46  # Processed clauses                    : 524
% 0.19/0.46  # ...of these trivial                  : 6
% 0.19/0.46  # ...subsumed                          : 159
% 0.19/0.46  # ...remaining for further processing  : 359
% 0.19/0.46  # Other redundant clauses eliminated   : 1
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 24
% 0.19/0.46  # Backward-rewritten                   : 120
% 0.19/0.46  # Generated clauses                    : 2080
% 0.19/0.46  # ...of the previous two non-trivial   : 2012
% 0.19/0.46  # Contextual simplify-reflections      : 2
% 0.19/0.46  # Paramodulations                      : 1984
% 0.19/0.46  # Factorizations                       : 6
% 0.19/0.46  # Equation resolutions                 : 89
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 213
% 0.19/0.46  #    Positive orientable unit clauses  : 15
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 10
% 0.19/0.46  #    Non-unit-clauses                  : 188
% 0.19/0.46  # Current number of unprocessed clauses: 1314
% 0.19/0.46  # ...number of literals in the above   : 7191
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 148
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 19025
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 7799
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 110
% 0.19/0.46  # Unit Clause-clause subsumption calls : 275
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 21
% 0.19/0.46  # BW rewrite match successes           : 6
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 35856
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.116 s
% 0.19/0.46  # System time              : 0.002 s
% 0.19/0.46  # Total time               : 0.118 s
% 0.19/0.46  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:17 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 156 expanded)
%              Number of clauses        :   38 (  60 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  245 ( 669 expanded)
%              Number of equality atoms :   40 ( 111 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(d2_orders_1,axiom,(
    ! [X1] : k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_orders_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t1_zfmisc_1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(s1_xboole_0__e5_6__mcart_1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X1))))))
        & ~ r1_xboole_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e5_6__mcart_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t79_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(fc9_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ~ v1_xboole_0(k4_orders_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

fof(c_0_15,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X36,X35)
        | m2_orders_2(X36,X33,X34)
        | X35 != k4_orders_2(X33,X34)
        | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) )
      & ( ~ m2_orders_2(X37,X33,X34)
        | r2_hidden(X37,X35)
        | X35 != k4_orders_2(X33,X34)
        | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) )
      & ( ~ r2_hidden(esk6_3(X33,X34,X38),X38)
        | ~ m2_orders_2(esk6_3(X33,X34,X38),X33,X34)
        | X38 = k4_orders_2(X33,X34)
        | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) )
      & ( r2_hidden(esk6_3(X33,X34,X38),X38)
        | m2_orders_2(esk6_3(X33,X34,X38),X33,X34)
        | X38 = k4_orders_2(X33,X34)
        | ~ m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

fof(c_0_16,plain,(
    ! [X40] : k1_orders_1(X40) = k7_subset_1(k1_zfmisc_1(X40),k9_setfam_1(X40),k1_tarski(k1_xboole_0)) ),
    inference(variable_rename,[status(thm)],[d2_orders_1])).

fof(c_0_17,plain,(
    ! [X22] : r1_tarski(X22,k1_zfmisc_1(k3_tarski(X22))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v3_orders_2(esk7_0)
    & v4_orders_2(esk7_0)
    & v5_orders_2(esk7_0)
    & l1_orders_2(esk7_0)
    & m1_orders_1(esk8_0,k1_orders_1(u1_struct_0(esk7_0)))
    & k3_tarski(k4_orders_2(esk7_0,esk8_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_19,plain,(
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

cnf(c_0_20,plain,
    ( m2_orders_2(X1,X3,X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k4_orders_2(X3,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X18,X19] :
      ( ( ~ r1_tarski(X18,k1_tarski(X19))
        | X18 = k1_xboole_0
        | X18 = k1_tarski(X19) )
      & ( X18 != k1_xboole_0
        | r1_tarski(X18,k1_tarski(X19)) )
      & ( X18 != k1_tarski(X19)
        | r1_tarski(X18,k1_tarski(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk7_0,esk8_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_28,plain,(
    ! [X25,X27,X28] :
      ( ( r2_hidden(X27,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X25))))))
        | ~ r2_hidden(X27,esk3_1(X25)) )
      & ( ~ r1_xboole_0(X27,X25)
        | ~ r2_hidden(X27,esk3_1(X25)) )
      & ( ~ r2_hidden(X28,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X25))))))
        | r1_xboole_0(X28,X25)
        | r2_hidden(X28,esk3_1(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e5_6__mcart_1])])])])])])])).

fof(c_0_29,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_30,plain,(
    ! [X43,X44,X45] :
      ( v2_struct_0(X43)
      | ~ v3_orders_2(X43)
      | ~ v4_orders_2(X43)
      | ~ v5_orders_2(X43)
      | ~ l1_orders_2(X43)
      | ~ m1_orders_1(X44,k1_orders_1(u1_struct_0(X43)))
      | ~ m2_orders_2(X45,X43,X44)
      | r2_hidden(k1_funct_1(X44,u1_struct_0(X43)),X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X3)
    | m2_orders_2(X1,X3,X4)
    | X2 != k4_orders_2(X3,X4)
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_orders_1(X4,k7_subset_1(k1_zfmisc_1(u1_struct_0(X3)),k9_setfam_1(u1_struct_0(X3)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k4_orders_2(esk7_0,esk8_0),k1_tarski(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_orders_1(esk8_0,k1_orders_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X1,esk3_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X9] : r1_xboole_0(X9,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( m2_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,k4_orders_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k4_orders_2(esk7_0,esk8_0) = k1_tarski(k1_xboole_0)
    | k4_orders_2(esk7_0,esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( m1_orders_1(esk8_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk7_0)),k9_setfam_1(u1_struct_0(esk7_0)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( v5_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( v4_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( v3_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_50,plain,
    ( esk3_1(X1) = k1_xboole_0
    | ~ r1_xboole_0(esk1_1(esk3_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_52,plain,(
    ! [X41,X42] :
      ( v2_struct_0(X41)
      | ~ v3_orders_2(X41)
      | ~ v4_orders_2(X41)
      | ~ v5_orders_2(X41)
      | ~ l1_orders_2(X41)
      | ~ m1_orders_1(X42,k1_orders_1(u1_struct_0(X41)))
      | ~ v1_xboole_0(k4_orders_2(X41,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( k4_orders_2(esk7_0,esk8_0) = k1_xboole_0
    | m2_orders_2(X1,esk7_0,esk8_0)
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_56,plain,
    ( esk3_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,u1_struct_0(esk7_0)),X1)
    | ~ m2_orders_2(X1,esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( k4_orders_2(esk7_0,esk8_0) = k1_xboole_0
    | m2_orders_2(k1_xboole_0,esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_56]),c_0_51])])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X2))
    | ~ m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( k4_orders_2(esk7_0,esk8_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_63])]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.14/0.39  # and selection function SelectNewComplexAHPNS.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.030 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 0.14/0.39  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 0.14/0.39  fof(d2_orders_1, axiom, ![X1]:k1_orders_1(X1)=k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_orders_1)).
% 0.14/0.39  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.14/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.39  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.14/0.39  fof(t1_zfmisc_1, axiom, k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 0.14/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.39  fof(s1_xboole_0__e5_6__mcart_1, axiom, ![X1]:?[X2]:![X3]:(r2_hidden(X3,X2)<=>(r2_hidden(X3,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X1))))))&~(r1_xboole_0(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e5_6__mcart_1)).
% 0.14/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.39  fof(t79_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 0.14/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.39  fof(fc9_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>~(v1_xboole_0(k4_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 0.14/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.14/0.39  fof(c_0_15, plain, ![X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X36,X35)|m2_orders_2(X36,X33,X34)|X35!=k4_orders_2(X33,X34)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)))&(~m2_orders_2(X37,X33,X34)|r2_hidden(X37,X35)|X35!=k4_orders_2(X33,X34)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33))))&((~r2_hidden(esk6_3(X33,X34,X38),X38)|~m2_orders_2(esk6_3(X33,X34,X38),X33,X34)|X38=k4_orders_2(X33,X34)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)))&(r2_hidden(esk6_3(X33,X34,X38),X38)|m2_orders_2(esk6_3(X33,X34,X38),X33,X34)|X38=k4_orders_2(X33,X34)|~m1_orders_1(X34,k1_orders_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.14/0.39  fof(c_0_16, plain, ![X40]:k1_orders_1(X40)=k7_subset_1(k1_zfmisc_1(X40),k9_setfam_1(X40),k1_tarski(k1_xboole_0)), inference(variable_rename,[status(thm)],[d2_orders_1])).
% 0.14/0.39  fof(c_0_17, plain, ![X22]:r1_tarski(X22,k1_zfmisc_1(k3_tarski(X22))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.14/0.39  fof(c_0_18, negated_conjecture, (((((~v2_struct_0(esk7_0)&v3_orders_2(esk7_0))&v4_orders_2(esk7_0))&v5_orders_2(esk7_0))&l1_orders_2(esk7_0))&(m1_orders_1(esk8_0,k1_orders_1(u1_struct_0(esk7_0)))&k3_tarski(k4_orders_2(esk7_0,esk8_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.14/0.39  fof(c_0_19, plain, ![X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X13,X12)|r1_tarski(X13,X11)|X12!=k1_zfmisc_1(X11))&(~r1_tarski(X14,X11)|r2_hidden(X14,X12)|X12!=k1_zfmisc_1(X11)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.39  cnf(c_0_20, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_21, plain, (k1_orders_1(X1)=k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  fof(c_0_22, plain, ![X18, X19]:((~r1_tarski(X18,k1_tarski(X19))|(X18=k1_xboole_0|X18=k1_tarski(X19)))&((X18!=k1_xboole_0|r1_tarski(X18,k1_tarski(X19)))&(X18!=k1_tarski(X19)|r1_tarski(X18,k1_tarski(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.14/0.39  cnf(c_0_23, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (k3_tarski(k4_orders_2(esk7_0,esk8_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_25, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[t1_zfmisc_1])).
% 0.14/0.39  cnf(c_0_26, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  fof(c_0_27, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.39  fof(c_0_28, plain, ![X25, X27, X28]:(((r2_hidden(X27,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X25))))))|~r2_hidden(X27,esk3_1(X25)))&(~r1_xboole_0(X27,X25)|~r2_hidden(X27,esk3_1(X25))))&(~r2_hidden(X28,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X25))))))|r1_xboole_0(X28,X25)|r2_hidden(X28,esk3_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[s1_xboole_0__e5_6__mcart_1])])])])])])])).
% 0.14/0.39  fof(c_0_29, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.39  fof(c_0_30, plain, ![X43, X44, X45]:(v2_struct_0(X43)|~v3_orders_2(X43)|~v4_orders_2(X43)|~v5_orders_2(X43)|~l1_orders_2(X43)|(~m1_orders_1(X44,k1_orders_1(u1_struct_0(X43)))|(~m2_orders_2(X45,X43,X44)|r2_hidden(k1_funct_1(X44,u1_struct_0(X43)),X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).
% 0.14/0.39  cnf(c_0_31, plain, (v2_struct_0(X3)|m2_orders_2(X1,X3,X4)|X2!=k4_orders_2(X3,X4)|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)|~r2_hidden(X1,X2)|~m1_orders_1(X4,k7_subset_1(k1_zfmisc_1(u1_struct_0(X3)),k9_setfam_1(u1_struct_0(X3)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.39  cnf(c_0_32, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (r1_tarski(k4_orders_2(esk7_0,esk8_0),k1_tarski(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (m1_orders_1(esk8_0,k1_orders_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_35, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_26])).
% 0.14/0.39  cnf(c_0_36, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.39  cnf(c_0_37, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X1,esk3_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_38, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.39  fof(c_0_39, plain, ![X9]:r1_xboole_0(X9,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.39  cnf(c_0_40, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_41, plain, (m2_orders_2(X1,X2,X3)|v2_struct_0(X2)|~m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,k4_orders_2(X2,X3))), inference(er,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (k4_orders_2(esk7_0,esk8_0)=k1_tarski(k1_xboole_0)|k4_orders_2(esk7_0,esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, (m1_orders_1(esk8_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk7_0)),k9_setfam_1(u1_struct_0(esk7_0)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_34, c_0_21])).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, (l1_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (v5_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (v4_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (v3_orders_2(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_49, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.39  cnf(c_0_50, plain, (esk3_1(X1)=k1_xboole_0|~r1_xboole_0(esk1_1(esk3_1(X1)),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.39  cnf(c_0_51, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.14/0.39  fof(c_0_52, plain, ![X41, X42]:(v2_struct_0(X41)|~v3_orders_2(X41)|~v4_orders_2(X41)|~v5_orders_2(X41)|~l1_orders_2(X41)|~m1_orders_1(X42,k1_orders_1(u1_struct_0(X41)))|~v1_xboole_0(k4_orders_2(X41,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).
% 0.14/0.39  cnf(c_0_53, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m2_orders_2(X3,X1,X2)|~m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_40, c_0_21])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (k4_orders_2(esk7_0,esk8_0)=k1_xboole_0|m2_orders_2(X1,esk7_0,esk8_0)|~r2_hidden(X1,k1_tarski(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])]), c_0_48])).
% 0.14/0.39  cnf(c_0_55, plain, (r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_49, c_0_25])).
% 0.14/0.39  cnf(c_0_56, plain, (esk3_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.14/0.39  cnf(c_0_57, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v1_xboole_0(k4_orders_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,u1_struct_0(esk7_0)),X1)|~m2_orders_2(X1,esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])]), c_0_48])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (k4_orders_2(esk7_0,esk8_0)=k1_xboole_0|m2_orders_2(k1_xboole_0,esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.39  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_56]), c_0_51])])).
% 0.14/0.39  cnf(c_0_61, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~v1_xboole_0(k4_orders_2(X1,X2))|~m1_orders_1(X2,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),k9_setfam_1(u1_struct_0(X1)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_57, c_0_21])).
% 0.14/0.39  cnf(c_0_62, negated_conjecture, (k4_orders_2(esk7_0,esk8_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.14/0.39  cnf(c_0_63, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.39  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_63])]), c_0_48]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 65
% 0.14/0.39  # Proof object clause steps            : 38
% 0.14/0.39  # Proof object formula steps           : 27
% 0.14/0.39  # Proof object conjectures             : 18
% 0.14/0.39  # Proof object clause conjectures      : 15
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 20
% 0.14/0.39  # Proof object initial formulas used   : 14
% 0.14/0.39  # Proof object generating inferences   : 12
% 0.14/0.39  # Proof object simplifying inferences  : 31
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 19
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 42
% 0.14/0.39  # Removed in clause preprocessing      : 2
% 0.14/0.39  # Initial clauses in saturation        : 40
% 0.14/0.39  # Processed clauses                    : 120
% 0.14/0.39  # ...of these trivial                  : 3
% 0.14/0.39  # ...subsumed                          : 4
% 0.14/0.39  # ...remaining for further processing  : 113
% 0.14/0.39  # Other redundant clauses eliminated   : 6
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 9
% 0.14/0.39  # Generated clauses                    : 132
% 0.14/0.39  # ...of the previous two non-trivial   : 111
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 124
% 0.14/0.39  # Factorizations                       : 2
% 0.14/0.39  # Equation resolutions                 : 6
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 59
% 0.14/0.39  #    Positive orientable unit clauses  : 25
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 4
% 0.14/0.39  #    Non-unit-clauses                  : 30
% 0.14/0.39  # Current number of unprocessed clauses: 66
% 0.14/0.39  # ...number of literals in the above   : 241
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 50
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 587
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 77
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.39  # Unit Clause-clause subsumption calls : 24
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 2
% 0.14/0.39  # BW rewrite match successes           : 2
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 5776
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.035 s
% 0.14/0.39  # System time              : 0.006 s
% 0.14/0.39  # Total time               : 0.041 s
% 0.14/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------

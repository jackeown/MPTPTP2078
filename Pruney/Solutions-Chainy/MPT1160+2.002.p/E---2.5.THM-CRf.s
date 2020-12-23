%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:54 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 822 expanded)
%              Number of clauses        :   48 ( 299 expanded)
%              Number of leaves         :   15 ( 204 expanded)
%              Depth                    :   14
%              Number of atoms          :  279 (3803 expanded)
%              Number of equality atoms :   27 ( 495 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_orders_2(X1,k1_struct_0(X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

fof(dt_k3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(d2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k1_struct_0(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t57_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(t10_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ~ ( X2 != k1_xboole_0
          & ! [X3] :
              ( m1_subset_1(X3,X1)
             => ~ r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k3_orders_2(X1,k1_struct_0(X1),X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t60_orders_2])).

fof(c_0_16,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v3_orders_2(X26)
      | ~ v4_orders_2(X26)
      | ~ v5_orders_2(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | m1_subset_1(k3_orders_2(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X22] :
      ( ~ l1_struct_0(X22)
      | k1_struct_0(X22) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).

fof(c_0_19,plain,(
    ! [X29] :
      ( ~ l1_orders_2(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_28,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_31,plain,(
    ! [X30,X31,X32,X33] :
      ( ( r2_orders_2(X30,X31,X32)
        | ~ r2_hidden(X31,k3_orders_2(X30,X33,X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( r2_hidden(X31,X33)
        | ~ r2_hidden(X31,k3_orders_2(X30,X33,X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30) )
      & ( ~ r2_orders_2(X30,X31,X32)
        | ~ r2_hidden(X31,X33)
        | r2_hidden(X31,k3_orders_2(X30,X33,X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

fof(c_0_32,plain,(
    ! [X13,X14] :
      ( ( m1_subset_1(esk1_2(X13,X14),X13)
        | X14 = k1_xboole_0
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | X14 = k1_xboole_0
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k3_orders_2(X3,X2,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk1_2(X1,X2),X1)
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k3_orders_2(esk2_0,k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25])])).

fof(c_0_43,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | m1_subset_1(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_49,plain,(
    ! [X23,X24,X25] :
      ( ( r1_orders_2(X23,X24,X25)
        | ~ r2_orders_2(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( X24 != X25
        | ~ r2_orders_2(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,X24,X25)
        | X24 = X25
        | r2_orders_2(X23,X24,X25)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),X1)
    | ~ r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_42])).

cnf(c_0_54,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_55,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X9,X8)
        | r2_hidden(X9,X8)
        | v1_xboole_0(X8) )
      & ( ~ r2_hidden(X9,X8)
        | m1_subset_1(X9,X8)
        | v1_xboole_0(X8) )
      & ( ~ m1_subset_1(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_xboole_0(X8) )
      & ( ~ v1_xboole_0(X9)
        | m1_subset_1(X9,X8)
        | ~ v1_xboole_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_34]),c_0_53])])).

cnf(c_0_58,plain,
    ( r2_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_54])).

fof(c_0_60,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_64,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_47]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_25])])).

fof(c_0_66,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ r2_hidden(X12,X11)
      | r2_hidden(X12,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_47]),c_0_65])).

cnf(c_0_70,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,k1_xboole_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_34])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_34])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,k3_orders_2(esk2_0,k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_71]),c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.41/0.57  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.41/0.57  # and selection function SelectNewComplexAHPNS.
% 0.41/0.57  #
% 0.41/0.57  # Preprocessing time       : 0.028 s
% 0.41/0.57  
% 0.41/0.57  # Proof found!
% 0.41/0.57  # SZS status Theorem
% 0.41/0.57  # SZS output start CNFRefutation
% 0.41/0.57  fof(t60_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_orders_2(X1,k1_struct_0(X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 0.41/0.57  fof(dt_k3_orders_2, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 0.41/0.57  fof(d2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k1_struct_0(X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 0.41/0.57  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.41/0.57  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.41/0.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.41/0.57  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.41/0.57  fof(t10_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 0.41/0.57  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.41/0.57  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.41/0.57  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.41/0.57  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.41/0.57  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.41/0.57  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.41/0.57  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.41/0.57  fof(c_0_15, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_orders_2(X1,k1_struct_0(X1),X2)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t60_orders_2])).
% 0.41/0.57  fof(c_0_16, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X28,u1_struct_0(X26))|m1_subset_1(k3_orders_2(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).
% 0.41/0.57  fof(c_0_17, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.41/0.57  fof(c_0_18, plain, ![X22]:(~l1_struct_0(X22)|k1_struct_0(X22)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).
% 0.41/0.57  fof(c_0_19, plain, ![X29]:(~l1_orders_2(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.41/0.57  cnf(c_0_20, plain, (v2_struct_0(X1)|m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.57  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.57  cnf(c_0_22, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.57  cnf(c_0_23, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.57  cnf(c_0_24, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.57  cnf(c_0_25, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.57  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.57  fof(c_0_27, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.41/0.57  cnf(c_0_28, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.57  cnf(c_0_29, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.41/0.57  fof(c_0_30, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.41/0.57  fof(c_0_31, plain, ![X30, X31, X32, X33]:(((r2_orders_2(X30,X31,X32)|~r2_hidden(X31,k3_orders_2(X30,X33,X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)))&(r2_hidden(X31,X33)|~r2_hidden(X31,k3_orders_2(X30,X33,X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30))))&(~r2_orders_2(X30,X31,X32)|~r2_hidden(X31,X33)|r2_hidden(X31,k3_orders_2(X30,X33,X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X30)))|~m1_subset_1(X32,u1_struct_0(X30))|~m1_subset_1(X31,u1_struct_0(X30))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.41/0.57  fof(c_0_32, plain, ![X13, X14]:((m1_subset_1(esk1_2(X13,X14),X13)|X14=k1_xboole_0|~m1_subset_1(X14,k1_zfmisc_1(X13)))&(r2_hidden(esk1_2(X13,X14),X14)|X14=k1_xboole_0|~m1_subset_1(X14,k1_zfmisc_1(X13)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_subset_1])])])])])).
% 0.41/0.57  cnf(c_0_33, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.41/0.57  cnf(c_0_34, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.41/0.57  cnf(c_0_35, negated_conjecture, (k3_orders_2(esk2_0,k1_struct_0(esk2_0),esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.57  cnf(c_0_36, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.41/0.57  fof(c_0_37, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.41/0.57  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.41/0.57  cnf(c_0_39, plain, (r2_hidden(X1,X2)|v2_struct_0(X3)|~r2_hidden(X1,k3_orders_2(X3,X2,X4))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.57  cnf(c_0_40, plain, (m1_subset_1(esk1_2(X1,X2),X1)|X2=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.57  cnf(c_0_41, negated_conjecture, (m1_subset_1(k3_orders_2(esk2_0,k1_xboole_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.41/0.57  cnf(c_0_42, negated_conjecture, (k3_orders_2(esk2_0,k1_xboole_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_25])])).
% 0.41/0.57  fof(c_0_43, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|m1_subset_1(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.41/0.57  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.41/0.57  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.41/0.57  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.41/0.57  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.41/0.57  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,X2),X2)|X2=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.41/0.57  fof(c_0_49, plain, ![X23, X24, X25]:(((r1_orders_2(X23,X24,X25)|~r2_orders_2(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|~l1_orders_2(X23))&(X24!=X25|~r2_orders_2(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|~l1_orders_2(X23)))&(~r1_orders_2(X23,X24,X25)|X24=X25|r2_orders_2(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|~l1_orders_2(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.41/0.57  cnf(c_0_50, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.41/0.57  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.41/0.57  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),X1)|~r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.41/0.57  cnf(c_0_53, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_41]), c_0_42])).
% 0.41/0.57  cnf(c_0_54, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.41/0.57  fof(c_0_55, plain, ![X8, X9]:(((~m1_subset_1(X9,X8)|r2_hidden(X9,X8)|v1_xboole_0(X8))&(~r2_hidden(X9,X8)|m1_subset_1(X9,X8)|v1_xboole_0(X8)))&((~m1_subset_1(X9,X8)|v1_xboole_0(X9)|~v1_xboole_0(X8))&(~v1_xboole_0(X9)|m1_subset_1(X9,X8)|~v1_xboole_0(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.41/0.57  cnf(c_0_56, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.41/0.57  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_34]), c_0_53])])).
% 0.41/0.57  cnf(c_0_58, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.41/0.57  cnf(c_0_59, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_54])).
% 0.41/0.57  fof(c_0_60, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.41/0.57  cnf(c_0_61, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.41/0.57  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.41/0.57  cnf(c_0_63, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.41/0.57  cnf(c_0_64, negated_conjecture, (r2_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)))|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_47]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.41/0.57  cnf(c_0_65, negated_conjecture, (~r2_orders_2(esk2_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_47]), c_0_25])])).
% 0.41/0.57  fof(c_0_66, plain, ![X10, X11, X12]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|(~r2_hidden(X12,X11)|r2_hidden(X12,X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.41/0.57  cnf(c_0_67, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.41/0.57  cnf(c_0_68, negated_conjecture, (v1_xboole_0(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.41/0.57  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,X1,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_47]), c_0_65])).
% 0.41/0.57  cnf(c_0_70, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.41/0.57  cnf(c_0_71, negated_conjecture, (esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.41/0.57  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0)),k3_orders_2(esk2_0,k1_xboole_0,esk1_2(u1_struct_0(esk2_0),k3_orders_2(esk2_0,k1_xboole_0,esk3_0))))), inference(spm,[status(thm)],[c_0_69, c_0_34])).
% 0.41/0.57  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_34])).
% 0.41/0.57  cnf(c_0_74, negated_conjecture, (r2_hidden(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_57, c_0_71])).
% 0.41/0.57  cnf(c_0_75, negated_conjecture, (~r2_hidden(k1_xboole_0,k3_orders_2(esk2_0,k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_71]), c_0_71])).
% 0.41/0.57  cnf(c_0_76, negated_conjecture, (r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.41/0.57  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), ['proof']).
% 0.41/0.57  # SZS output end CNFRefutation
% 0.41/0.57  # Proof object total steps             : 78
% 0.41/0.57  # Proof object clause steps            : 48
% 0.41/0.57  # Proof object formula steps           : 30
% 0.41/0.57  # Proof object conjectures             : 29
% 0.41/0.57  # Proof object clause conjectures      : 26
% 0.41/0.57  # Proof object formula conjectures     : 3
% 0.41/0.57  # Proof object initial clauses used    : 23
% 0.41/0.57  # Proof object initial formulas used   : 15
% 0.41/0.57  # Proof object generating inferences   : 20
% 0.41/0.57  # Proof object simplifying inferences  : 36
% 0.41/0.57  # Training examples: 0 positive, 0 negative
% 0.41/0.57  # Parsed axioms                        : 15
% 0.41/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.57  # Initial clauses                      : 32
% 0.41/0.57  # Removed in clause preprocessing      : 0
% 0.41/0.57  # Initial clauses in saturation        : 32
% 0.41/0.57  # Processed clauses                    : 1539
% 0.41/0.57  # ...of these trivial                  : 13
% 0.41/0.57  # ...subsumed                          : 474
% 0.41/0.57  # ...remaining for further processing  : 1052
% 0.41/0.57  # Other redundant clauses eliminated   : 3
% 0.41/0.57  # Clauses deleted for lack of memory   : 0
% 0.41/0.57  # Backward-subsumed                    : 36
% 0.41/0.57  # Backward-rewritten                   : 560
% 0.41/0.57  # Generated clauses                    : 6395
% 0.41/0.57  # ...of the previous two non-trivial   : 6111
% 0.41/0.57  # Contextual simplify-reflections      : 17
% 0.41/0.57  # Paramodulations                      : 6392
% 0.41/0.57  # Factorizations                       : 0
% 0.41/0.57  # Equation resolutions                 : 3
% 0.41/0.57  # Propositional unsat checks           : 0
% 0.41/0.57  #    Propositional check models        : 0
% 0.41/0.57  #    Propositional check unsatisfiable : 0
% 0.41/0.57  #    Propositional clauses             : 0
% 0.41/0.57  #    Propositional clauses after purity: 0
% 0.41/0.57  #    Propositional unsat core size     : 0
% 0.41/0.57  #    Propositional preprocessing time  : 0.000
% 0.41/0.57  #    Propositional encoding time       : 0.000
% 0.41/0.57  #    Propositional solver time         : 0.000
% 0.41/0.57  #    Success case prop preproc time    : 0.000
% 0.41/0.57  #    Success case prop encoding time   : 0.000
% 0.41/0.57  #    Success case prop solver time     : 0.000
% 0.41/0.57  # Current number of processed clauses  : 453
% 0.41/0.57  #    Positive orientable unit clauses  : 65
% 0.41/0.57  #    Positive unorientable unit clauses: 0
% 0.41/0.57  #    Negative unit clauses             : 49
% 0.41/0.57  #    Non-unit-clauses                  : 339
% 0.41/0.57  # Current number of unprocessed clauses: 4589
% 0.41/0.57  # ...number of literals in the above   : 17107
% 0.41/0.57  # Current number of archived formulas  : 0
% 0.41/0.57  # Current number of archived clauses   : 596
% 0.41/0.57  # Clause-clause subsumption calls (NU) : 73117
% 0.41/0.57  # Rec. Clause-clause subsumption calls : 42873
% 0.41/0.57  # Non-unit clause-clause subsumptions  : 493
% 0.41/0.57  # Unit Clause-clause subsumption calls : 6387
% 0.41/0.57  # Rewrite failures with RHS unbound    : 0
% 0.41/0.57  # BW rewrite match attempts            : 2609
% 0.41/0.57  # BW rewrite match successes           : 40
% 0.41/0.57  # Condensation attempts                : 1539
% 0.41/0.57  # Condensation successes               : 0
% 0.41/0.57  # Termbank termtop insertions          : 296696
% 0.41/0.57  
% 0.41/0.57  # -------------------------------------------------
% 0.41/0.57  # User time                : 0.220 s
% 0.41/0.57  # System time              : 0.011 s
% 0.41/0.57  # Total time               : 0.231 s
% 0.41/0.57  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

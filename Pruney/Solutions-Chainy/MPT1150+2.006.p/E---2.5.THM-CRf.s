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
% DateTime   : Thu Dec  3 11:09:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 438 expanded)
%              Number of clauses        :   41 ( 169 expanded)
%              Number of leaves         :   12 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :  280 (1860 expanded)
%              Number of equality atoms :   36 ( 315 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(d12_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(fraenkel_a_2_0_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X5,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k1_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_orders_2])).

fof(c_0_13,plain,(
    ! [X30] :
      ( ~ l1_orders_2(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & k1_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X22] :
      ( ~ l1_struct_0(X22)
      | k2_struct_0(X22) = u1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v3_orders_2(X26)
      | ~ v4_orders_2(X26)
      | ~ v5_orders_2(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | k1_orders_2(X26,X27) = a_2_0_orders_2(X26,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X31,X32,X33,X35,X36] :
      ( ( m1_subset_1(esk2_3(X31,X32,X33),u1_struct_0(X32))
        | ~ r2_hidden(X31,a_2_0_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( X31 = esk2_3(X31,X32,X33)
        | ~ r2_hidden(X31,a_2_0_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r2_hidden(X35,X33)
        | r2_orders_2(X32,X35,esk2_3(X31,X32,X33))
        | ~ r2_hidden(X31,a_2_0_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( m1_subset_1(esk3_4(X31,X32,X33,X36),u1_struct_0(X32))
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_0_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( r2_hidden(esk3_4(X31,X32,X33,X36),X33)
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_0_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( ~ r2_orders_2(X32,esk3_4(X31,X32,X33,X36),X36)
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_0_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

fof(c_0_23,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | m1_subset_1(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_24,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r2_orders_2(X2,X1,esk2_3(X4,X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( k1_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( k2_struct_0(esk4_0) = u1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( k1_orders_2(esk4_0,X1) = a_2_0_orders_2(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_18])]),c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ v3_orders_2(X28)
      | ~ v4_orders_2(X28)
      | ~ v5_orders_2(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | m1_subset_1(k1_orders_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r2_orders_2(X1,X2,esk2_3(X3,X1,X4))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( esk2_3(X1,esk4_0,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,a_2_0_orders_2(esk4_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_28]),c_0_29]),c_0_18])]),c_0_30])).

fof(c_0_43,plain,(
    ! [X6] :
      ( X6 = k1_xboole_0
      | r2_hidden(esk1_1(X6),X6) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_44,negated_conjecture,
    ( k1_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k1_orders_2(esk4_0,u1_struct_0(esk4_0)) = a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_46,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r2_orders_2(esk4_0,X1,esk2_3(X2,esk4_0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X2,a_2_0_orders_2(esk4_0,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_28]),c_0_29]),c_0_18])]),c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( esk2_3(X1,esk4_0,u1_struct_0(esk4_0)) = X1
    | ~ r2_hidden(X1,a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_27]),c_0_28]),c_0_29]),c_0_18]),c_0_39])]),c_0_30])).

fof(c_0_54,plain,(
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

cnf(c_0_55,negated_conjecture,
    ( r2_orders_2(esk4_0,X1,esk2_3(X2,esk4_0,u1_struct_0(esk4_0)))
    | ~ r2_hidden(X2,a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)) = esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r2_orders_2(esk4_0,X1,esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_56]),c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_50]),c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_53])).

cnf(c_0_62,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r2_orders_2(esk4_0,esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_50]),c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_18]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:00:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.38  # and selection function PSelectComplexPreferEQ.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t44_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 0.19/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.38  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.19/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.38  fof(dt_k1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 0.19/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.38  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t44_orders_2])).
% 0.19/0.38  fof(c_0_13, plain, ![X30]:(~l1_orders_2(X30)|l1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.38  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&k1_orders_2(esk4_0,k2_struct_0(esk4_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X22]:(~l1_struct_0(X22)|k2_struct_0(X22)=u1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.38  cnf(c_0_17, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_19, plain, ![X26, X27]:(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|k1_orders_2(X26,X27)=a_2_0_orders_2(X26,X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.19/0.38  fof(c_0_20, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_22, plain, ![X31, X32, X33, X35, X36]:((((m1_subset_1(esk2_3(X31,X32,X33),u1_struct_0(X32))|~r2_hidden(X31,a_2_0_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))))&(X31=esk2_3(X31,X32,X33)|~r2_hidden(X31,a_2_0_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))))))&(~m1_subset_1(X35,u1_struct_0(X32))|(~r2_hidden(X35,X33)|r2_orders_2(X32,X35,esk2_3(X31,X32,X33)))|~r2_hidden(X31,a_2_0_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))))))&((m1_subset_1(esk3_4(X31,X32,X33,X36),u1_struct_0(X32))|(~m1_subset_1(X36,u1_struct_0(X32))|X31!=X36)|r2_hidden(X31,a_2_0_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))))&((r2_hidden(esk3_4(X31,X32,X33,X36),X33)|(~m1_subset_1(X36,u1_struct_0(X32))|X31!=X36)|r2_hidden(X31,a_2_0_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))))&(~r2_orders_2(X32,esk3_4(X31,X32,X33,X36),X36)|(~m1_subset_1(X36,u1_struct_0(X32))|X31!=X36)|r2_hidden(X31,a_2_0_orders_2(X32,X33))|(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.19/0.38  fof(c_0_23, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|m1_subset_1(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.38  cnf(c_0_24, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.38  cnf(c_0_26, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_33, plain, (r2_orders_2(X2,X1,esk2_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_34, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_35, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k1_orders_2(esk4_0,k2_struct_0(esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (k2_struct_0(esk4_0)=u1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (k1_orders_2(esk4_0,X1)=a_2_0_orders_2(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_18])]), c_0_30])).
% 0.19/0.38  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.38  fof(c_0_40, plain, ![X28, X29]:(v2_struct_0(X28)|~v3_orders_2(X28)|~v4_orders_2(X28)|~v5_orders_2(X28)|~l1_orders_2(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|m1_subset_1(k1_orders_2(X28,X29),k1_zfmisc_1(u1_struct_0(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).
% 0.19/0.38  cnf(c_0_41, plain, (v2_struct_0(X1)|r2_orders_2(X1,X2,esk2_3(X3,X1,X4))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,X4))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (esk2_3(X1,esk4_0,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,a_2_0_orders_2(esk4_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_28]), c_0_29]), c_0_18])]), c_0_30])).
% 0.19/0.38  fof(c_0_43, plain, ![X6]:(X6=k1_xboole_0|r2_hidden(esk1_1(X6),X6)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k1_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (k1_orders_2(esk4_0,u1_struct_0(esk4_0))=a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  fof(c_0_46, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.38  cnf(c_0_47, plain, (v2_struct_0(X1)|m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (r2_orders_2(esk4_0,X1,esk2_3(X2,esk4_0,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X2,a_2_0_orders_2(esk4_0,X3))|~r2_hidden(X1,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_27]), c_0_28]), c_0_29]), c_0_18])]), c_0_30])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (esk2_3(X1,esk4_0,u1_struct_0(esk4_0))=X1|~r2_hidden(X1,a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 0.19/0.38  cnf(c_0_50, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.38  cnf(c_0_52, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_27]), c_0_28]), c_0_29]), c_0_18]), c_0_39])]), c_0_30])).
% 0.19/0.38  fof(c_0_54, plain, ![X23, X24, X25]:(((r1_orders_2(X23,X24,X25)|~r2_orders_2(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|~l1_orders_2(X23))&(X24!=X25|~r2_orders_2(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|~l1_orders_2(X23)))&(~r1_orders_2(X23,X24,X25)|X24=X25|r2_orders_2(X23,X24,X25)|~m1_subset_1(X25,u1_struct_0(X23))|~m1_subset_1(X24,u1_struct_0(X23))|~l1_orders_2(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (r2_orders_2(esk4_0,X1,esk2_3(X2,esk4_0,u1_struct_0(esk4_0)))|~r2_hidden(X2,a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_39])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0))=esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.38  cnf(c_0_58, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (r2_orders_2(esk4_0,X1,esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_50]), c_0_56]), c_0_51])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_50]), c_0_51])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_34, c_0_53])).
% 0.19/0.38  cnf(c_0_62, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_58])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (r2_orders_2(esk4_0,esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_50]), c_0_51])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_18]), c_0_64])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 66
% 0.19/0.38  # Proof object clause steps            : 41
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 28
% 0.19/0.38  # Proof object clause conjectures      : 25
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 18
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 18
% 0.19/0.38  # Proof object simplifying inferences  : 35
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 15
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 30
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 30
% 0.19/0.38  # Processed clauses                    : 168
% 0.19/0.38  # ...of these trivial                  : 8
% 0.19/0.38  # ...subsumed                          : 8
% 0.19/0.38  # ...remaining for further processing  : 152
% 0.19/0.38  # Other redundant clauses eliminated   : 6
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 2
% 0.19/0.38  # Generated clauses                    : 194
% 0.19/0.38  # ...of the previous two non-trivial   : 170
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 188
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 6
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 115
% 0.19/0.38  #    Positive orientable unit clauses  : 35
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 11
% 0.19/0.38  #    Non-unit-clauses                  : 69
% 0.19/0.38  # Current number of unprocessed clauses: 60
% 0.19/0.38  # ...number of literals in the above   : 146
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 31
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1436
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 327
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.19/0.38  # Unit Clause-clause subsumption calls : 17
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 34
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7629
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.038 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.044 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

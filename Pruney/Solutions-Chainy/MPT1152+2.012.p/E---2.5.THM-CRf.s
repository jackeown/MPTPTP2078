%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 552 expanded)
%              Number of clauses        :   41 ( 204 expanded)
%              Number of leaves         :   13 ( 136 expanded)
%              Depth                    :   12
%              Number of atoms          :  281 (2210 expanded)
%              Number of equality atoms :   40 ( 401 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k2_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(d13_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(fraenkel_a_2_1_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(dt_k2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k2_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t46_orders_2])).

fof(c_0_14,plain,(
    ! [X28] :
      ( ~ l1_orders_2(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & k2_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X20] :
      ( ~ l1_struct_0(X20)
      | k2_struct_0(X20) = u1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v3_orders_2(X24)
      | ~ v4_orders_2(X24)
      | ~ v5_orders_2(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | k2_orders_2(X24,X25) = a_2_1_orders_2(X24,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_21,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_22,plain,(
    ! [X29,X30,X31,X33,X34] :
      ( ( m1_subset_1(esk2_3(X29,X30,X31),u1_struct_0(X30))
        | ~ r2_hidden(X29,a_2_1_orders_2(X30,X31))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) )
      & ( X29 = esk2_3(X29,X30,X31)
        | ~ r2_hidden(X29,a_2_1_orders_2(X30,X31))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ r2_hidden(X33,X31)
        | r2_orders_2(X30,esk2_3(X29,X30,X31),X33)
        | ~ r2_hidden(X29,a_2_1_orders_2(X30,X31))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) )
      & ( m1_subset_1(esk3_4(X29,X30,X31,X34),u1_struct_0(X30))
        | ~ m1_subset_1(X34,u1_struct_0(X30))
        | X29 != X34
        | r2_hidden(X29,a_2_1_orders_2(X30,X31))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) )
      & ( r2_hidden(esk3_4(X29,X30,X31,X34),X31)
        | ~ m1_subset_1(X34,u1_struct_0(X30))
        | X29 != X34
        | r2_hidden(X29,a_2_1_orders_2(X30,X31))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) )
      & ( ~ r2_orders_2(X30,X34,esk3_4(X29,X30,X31,X34))
        | ~ m1_subset_1(X34,u1_struct_0(X30))
        | X29 != X34
        | r2_hidden(X29,a_2_1_orders_2(X30,X31))
        | v2_struct_0(X30)
        | ~ v3_orders_2(X30)
        | ~ v4_orders_2(X30)
        | ~ v5_orders_2(X30)
        | ~ l1_orders_2(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

cnf(c_0_23,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k2_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( k2_struct_0(esk4_0) = u1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k2_orders_2(esk4_0,X1) = a_2_1_orders_2(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_18])]),c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v3_orders_2(X26)
      | ~ v4_orders_2(X26)
      | ~ v5_orders_2(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | m1_subset_1(k2_orders_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).

fof(c_0_38,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_39,negated_conjecture,
    ( esk2_3(X1,esk4_0,X2) = X1
    | ~ r2_hidden(X1,a_2_1_orders_2(esk4_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_27]),c_0_28]),c_0_18])]),c_0_29])).

fof(c_0_40,plain,(
    ! [X16,X18,X19] :
      ( ( r2_hidden(esk1_1(X16),X16)
        | X16 = k1_xboole_0 )
      & ( ~ r2_hidden(X18,X16)
        | esk1_1(X16) != k4_tarski(X18,X19)
        | X16 = k1_xboole_0 )
      & ( ~ r2_hidden(X19,X16)
        | esk1_1(X16) != k4_tarski(X18,X19)
        | X16 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_41,negated_conjecture,
    ( k2_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k2_orders_2(esk4_0,u1_struct_0(esk4_0)) = a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | ~ v1_xboole_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_45,plain,
    ( r2_orders_2(X2,esk2_3(X4,X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( esk2_3(X1,esk4_0,u1_struct_0(esk4_0)) = X1
    | ~ r2_hidden(X1,a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_26]),c_0_27]),c_0_28]),c_0_18]),c_0_36])]),c_0_29])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r2_orders_2(X1,esk2_3(X2,X1,X3),X4)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( esk2_3(esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)) = esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_54,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_50])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

fof(c_0_57,plain,(
    ! [X21,X22,X23] :
      ( ( r1_orders_2(X21,X22,X23)
        | ~ r2_orders_2(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( X22 != X23
        | ~ r2_orders_2(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) )
      & ( ~ r1_orders_2(X21,X22,X23)
        | X22 = X23
        | r2_orders_2(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_58,negated_conjecture,
    ( r2_orders_2(esk4_0,esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),X1)
    | ~ r2_hidden(esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_26]),c_0_27]),c_0_28]),c_0_18]),c_0_36])]),c_0_29])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_50]),c_0_49])).

cnf(c_0_62,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_orders_2(esk4_0,esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),X1)
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_48]),c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_65,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r2_orders_2(esk4_0,esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_18]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.13/0.40  # and selection function PSelectComplexPreferEQ.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t46_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k2_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 0.13/0.40  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.40  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.40  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 0.13/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.40  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.13/0.40  fof(dt_k2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 0.13/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.40  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.13/0.40  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.40  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.13/0.40  fof(c_0_13, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k2_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t46_orders_2])).
% 0.13/0.40  fof(c_0_14, plain, ![X28]:(~l1_orders_2(X28)|l1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.40  fof(c_0_15, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&k2_orders_2(esk4_0,k2_struct_0(esk4_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.40  fof(c_0_16, plain, ![X20]:(~l1_struct_0(X20)|k2_struct_0(X20)=u1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.40  cnf(c_0_17, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_19, plain, ![X24, X25]:(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|k2_orders_2(X24,X25)=a_2_1_orders_2(X24,X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.13/0.40  fof(c_0_20, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.40  fof(c_0_21, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.40  fof(c_0_22, plain, ![X29, X30, X31, X33, X34]:((((m1_subset_1(esk2_3(X29,X30,X31),u1_struct_0(X30))|~r2_hidden(X29,a_2_1_orders_2(X30,X31))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))))&(X29=esk2_3(X29,X30,X31)|~r2_hidden(X29,a_2_1_orders_2(X30,X31))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))))))&(~m1_subset_1(X33,u1_struct_0(X30))|(~r2_hidden(X33,X31)|r2_orders_2(X30,esk2_3(X29,X30,X31),X33))|~r2_hidden(X29,a_2_1_orders_2(X30,X31))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30))))))&((m1_subset_1(esk3_4(X29,X30,X31,X34),u1_struct_0(X30))|(~m1_subset_1(X34,u1_struct_0(X30))|X29!=X34)|r2_hidden(X29,a_2_1_orders_2(X30,X31))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))))&((r2_hidden(esk3_4(X29,X30,X31,X34),X31)|(~m1_subset_1(X34,u1_struct_0(X30))|X29!=X34)|r2_hidden(X29,a_2_1_orders_2(X30,X31))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))))&(~r2_orders_2(X30,X34,esk3_4(X29,X30,X31,X34))|(~m1_subset_1(X34,u1_struct_0(X30))|X29!=X34)|r2_hidden(X29,a_2_1_orders_2(X30,X31))|(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.13/0.40  cnf(c_0_23, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.40  cnf(c_0_25, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_30, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_31, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_32, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (k2_orders_2(esk4_0,k2_struct_0(esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (k2_struct_0(esk4_0)=u1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (k2_orders_2(esk4_0,X1)=a_2_1_orders_2(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_18])]), c_0_29])).
% 0.13/0.40  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.40  fof(c_0_37, plain, ![X26, X27]:(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|m1_subset_1(k2_orders_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).
% 0.13/0.40  fof(c_0_38, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (esk2_3(X1,esk4_0,X2)=X1|~r2_hidden(X1,a_2_1_orders_2(esk4_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_27]), c_0_28]), c_0_18])]), c_0_29])).
% 0.13/0.40  fof(c_0_40, plain, ![X16, X18, X19]:((r2_hidden(esk1_1(X16),X16)|X16=k1_xboole_0)&((~r2_hidden(X18,X16)|esk1_1(X16)!=k4_tarski(X18,X19)|X16=k1_xboole_0)&(~r2_hidden(X19,X16)|esk1_1(X16)!=k4_tarski(X18,X19)|X16=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (k2_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (k2_orders_2(esk4_0,u1_struct_0(esk4_0))=a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.40  cnf(c_0_43, plain, (v2_struct_0(X1)|m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.40  fof(c_0_44, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|~v1_xboole_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.40  cnf(c_0_45, plain, (r2_orders_2(X2,esk2_3(X4,X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_46, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (esk2_3(X1,esk4_0,u1_struct_0(esk4_0))=X1|~r2_hidden(X1,a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 0.13/0.40  cnf(c_0_48, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (m1_subset_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_42]), c_0_26]), c_0_27]), c_0_28]), c_0_18]), c_0_36])]), c_0_29])).
% 0.13/0.40  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  cnf(c_0_52, plain, (v2_struct_0(X1)|r2_orders_2(X1,esk2_3(X2,X1,X3),X4)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X2,a_2_1_orders_2(X1,X3))|~r2_hidden(X4,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (esk2_3(esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0))=esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.13/0.40  fof(c_0_54, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_46, c_0_50])).
% 0.13/0.40  cnf(c_0_56, plain, (X1=k1_xboole_0|~v1_xboole_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 0.13/0.40  fof(c_0_57, plain, ![X21, X22, X23]:(((r1_orders_2(X21,X22,X23)|~r2_orders_2(X21,X22,X23)|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21))&(X22!=X23|~r2_orders_2(X21,X22,X23)|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21)))&(~r1_orders_2(X21,X22,X23)|X22=X23|r2_orders_2(X21,X22,X23)|~m1_subset_1(X23,u1_struct_0(X21))|~m1_subset_1(X22,u1_struct_0(X21))|~l1_orders_2(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (r2_orders_2(esk4_0,esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),X1)|~r2_hidden(esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0)))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_26]), c_0_27]), c_0_28]), c_0_18]), c_0_36])]), c_0_29])).
% 0.13/0.40  cnf(c_0_59, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_48]), c_0_49])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_50]), c_0_49])).
% 0.13/0.40  cnf(c_0_62, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r2_orders_2(esk4_0,esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),X1)|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_48]), c_0_49])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.13/0.40  cnf(c_0_65, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_62])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (r2_orders_2(esk4_0,esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))),esk1_1(a_2_1_orders_2(esk4_0,u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_18]), c_0_60])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 68
% 0.13/0.40  # Proof object clause steps            : 41
% 0.13/0.40  # Proof object formula steps           : 27
% 0.13/0.40  # Proof object conjectures             : 27
% 0.13/0.40  # Proof object clause conjectures      : 24
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 19
% 0.13/0.40  # Proof object initial formulas used   : 13
% 0.13/0.40  # Proof object generating inferences   : 17
% 0.13/0.40  # Proof object simplifying inferences  : 37
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 13
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 27
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 26
% 0.13/0.40  # Processed clauses                    : 265
% 0.13/0.40  # ...of these trivial                  : 5
% 0.13/0.40  # ...subsumed                          : 74
% 0.13/0.40  # ...remaining for further processing  : 186
% 0.13/0.40  # Other redundant clauses eliminated   : 4
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 2
% 0.13/0.40  # Backward-rewritten                   : 9
% 0.13/0.40  # Generated clauses                    : 568
% 0.13/0.40  # ...of the previous two non-trivial   : 557
% 0.13/0.40  # Contextual simplify-reflections      : 3
% 0.13/0.40  # Paramodulations                      : 564
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 4
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 145
% 0.13/0.40  #    Positive orientable unit clauses  : 22
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 120
% 0.13/0.40  # Current number of unprocessed clauses: 333
% 0.13/0.40  # ...number of literals in the above   : 986
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 38
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 3402
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 2093
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 49
% 0.13/0.40  # Unit Clause-clause subsumption calls : 39
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 23
% 0.13/0.40  # BW rewrite match successes           : 4
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 19347
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.050 s
% 0.13/0.40  # System time              : 0.005 s
% 0.13/0.40  # Total time               : 0.055 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------

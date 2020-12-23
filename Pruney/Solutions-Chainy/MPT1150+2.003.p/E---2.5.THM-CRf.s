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
% DateTime   : Thu Dec  3 11:09:34 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 442 expanded)
%              Number of clauses        :   43 ( 171 expanded)
%              Number of leaves         :   12 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  297 (1910 expanded)
%              Number of equality atoms :   42 ( 336 expanded)
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    ! [X35] :
      ( ~ l1_orders_2(X35)
      | l1_struct_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X27] :
      ( ~ l1_struct_0(X27)
      | k2_struct_0(X27) = u1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( v2_struct_0(X31)
      | ~ v3_orders_2(X31)
      | ~ v4_orders_2(X31)
      | ~ v5_orders_2(X31)
      | ~ l1_orders_2(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | k1_orders_2(X31,X32) = a_2_0_orders_2(X31,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X36,X37,X38,X40,X41] :
      ( ( m1_subset_1(esk3_3(X36,X37,X38),u1_struct_0(X37))
        | ~ r2_hidden(X36,a_2_0_orders_2(X37,X38))
        | v2_struct_0(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))) )
      & ( X36 = esk3_3(X36,X37,X38)
        | ~ r2_hidden(X36,a_2_0_orders_2(X37,X38))
        | v2_struct_0(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))) )
      & ( ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ r2_hidden(X40,X38)
        | r2_orders_2(X37,X40,esk3_3(X36,X37,X38))
        | ~ r2_hidden(X36,a_2_0_orders_2(X37,X38))
        | v2_struct_0(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))) )
      & ( m1_subset_1(esk4_4(X36,X37,X38,X41),u1_struct_0(X37))
        | ~ m1_subset_1(X41,u1_struct_0(X37))
        | X36 != X41
        | r2_hidden(X36,a_2_0_orders_2(X37,X38))
        | v2_struct_0(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))) )
      & ( r2_hidden(esk4_4(X36,X37,X38,X41),X38)
        | ~ m1_subset_1(X41,u1_struct_0(X37))
        | X36 != X41
        | r2_hidden(X36,a_2_0_orders_2(X37,X38))
        | v2_struct_0(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))) )
      & ( ~ r2_orders_2(X37,esk4_4(X36,X37,X38,X41),X41)
        | ~ m1_subset_1(X41,u1_struct_0(X37))
        | X36 != X41
        | r2_hidden(X36,a_2_0_orders_2(X37,X38))
        | v2_struct_0(X37)
        | ~ v3_orders_2(X37)
        | ~ v4_orders_2(X37)
        | ~ v5_orders_2(X37)
        | ~ l1_orders_2(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

fof(c_0_23,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_24,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
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
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r2_orders_2(X2,X1,esk3_3(X4,X2,X3))
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
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( k2_struct_0(esk5_0) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( k1_orders_2(esk5_0,X1) = a_2_0_orders_2(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_18])]),c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X33,X34] :
      ( v2_struct_0(X33)
      | ~ v3_orders_2(X33)
      | ~ v4_orders_2(X33)
      | ~ v5_orders_2(X33)
      | ~ l1_orders_2(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | m1_subset_1(k1_orders_2(X33,X34),k1_zfmisc_1(u1_struct_0(X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r2_orders_2(X1,X2,esk3_3(X3,X1,X4))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( esk3_3(X1,esk5_0,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,a_2_0_orders_2(esk5_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_28]),c_0_29]),c_0_18])]),c_0_30])).

fof(c_0_43,plain,(
    ! [X23,X25,X26] :
      ( ( r2_hidden(esk2_1(X23),X23)
        | X23 = k1_xboole_0 )
      & ( ~ r2_hidden(X25,X23)
        | esk2_1(X23) != k4_tarski(X25,X26)
        | X23 = k1_xboole_0 )
      & ( ~ r2_hidden(X26,X23)
        | esk2_1(X23) != k4_tarski(X25,X26)
        | X23 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_44,negated_conjecture,
    ( k1_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k1_orders_2(esk5_0,u1_struct_0(esk5_0)) = a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_46,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

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
    ( r2_orders_2(esk5_0,X1,esk3_3(X2,esk5_0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,a_2_0_orders_2(esk5_0,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_28]),c_0_29]),c_0_18])]),c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( esk3_3(X1,esk5_0,u1_struct_0(esk5_0)) = X1
    | ~ r2_hidden(X1,a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_27]),c_0_28]),c_0_29]),c_0_18]),c_0_39])]),c_0_30])).

fof(c_0_55,plain,(
    ! [X28,X29,X30] :
      ( ( r1_orders_2(X28,X29,X30)
        | ~ r2_orders_2(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( X29 != X30
        | ~ r2_orders_2(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( ~ r1_orders_2(X28,X29,X30)
        | X29 = X30
        | r2_orders_2(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_56,negated_conjecture,
    ( r2_orders_2(esk5_0,X1,esk3_3(X2,esk5_0,u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)) = esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r2_orders_2(esk5_0,X1,esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_50]),c_0_51]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_54])).

cnf(c_0_64,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_orders_2(esk5_0,esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_50]),c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_18]),c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n008.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 15:54:30 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  # Version: 2.5pre002
% 0.10/0.31  # No SInE strategy applied
% 0.10/0.31  # Trying AutoSched0 for 299 seconds
% 0.10/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.10/0.36  # and selection function PSelectComplexPreferEQ.
% 0.10/0.36  #
% 0.10/0.36  # Preprocessing time       : 0.018 s
% 0.10/0.36  # Presaturation interreduction done
% 0.10/0.36  
% 0.10/0.36  # Proof found!
% 0.10/0.36  # SZS status Theorem
% 0.10/0.36  # SZS output start CNFRefutation
% 0.10/0.36  fof(t44_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 0.10/0.36  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.10/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.10/0.36  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.10/0.36  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 0.10/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.10/0.36  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.10/0.36  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.10/0.36  fof(dt_k1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 0.10/0.36  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.10/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.10/0.36  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.10/0.36  fof(c_0_12, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t44_orders_2])).
% 0.10/0.36  fof(c_0_13, plain, ![X35]:(~l1_orders_2(X35)|l1_struct_0(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.10/0.36  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.10/0.36  fof(c_0_15, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.10/0.36  fof(c_0_16, plain, ![X27]:(~l1_struct_0(X27)|k2_struct_0(X27)=u1_struct_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.10/0.36  cnf(c_0_17, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.36  cnf(c_0_18, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  fof(c_0_19, plain, ![X31, X32]:(v2_struct_0(X31)|~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~l1_orders_2(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|k1_orders_2(X31,X32)=a_2_0_orders_2(X31,X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.10/0.36  fof(c_0_20, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.10/0.36  cnf(c_0_21, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.10/0.36  fof(c_0_22, plain, ![X36, X37, X38, X40, X41]:((((m1_subset_1(esk3_3(X36,X37,X38),u1_struct_0(X37))|~r2_hidden(X36,a_2_0_orders_2(X37,X38))|(v2_struct_0(X37)|~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~l1_orders_2(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))))&(X36=esk3_3(X36,X37,X38)|~r2_hidden(X36,a_2_0_orders_2(X37,X38))|(v2_struct_0(X37)|~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~l1_orders_2(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))))))&(~m1_subset_1(X40,u1_struct_0(X37))|(~r2_hidden(X40,X38)|r2_orders_2(X37,X40,esk3_3(X36,X37,X38)))|~r2_hidden(X36,a_2_0_orders_2(X37,X38))|(v2_struct_0(X37)|~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~l1_orders_2(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37))))))&((m1_subset_1(esk4_4(X36,X37,X38,X41),u1_struct_0(X37))|(~m1_subset_1(X41,u1_struct_0(X37))|X36!=X41)|r2_hidden(X36,a_2_0_orders_2(X37,X38))|(v2_struct_0(X37)|~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~l1_orders_2(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))))&((r2_hidden(esk4_4(X36,X37,X38,X41),X38)|(~m1_subset_1(X41,u1_struct_0(X37))|X36!=X41)|r2_hidden(X36,a_2_0_orders_2(X37,X38))|(v2_struct_0(X37)|~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~l1_orders_2(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))))&(~r2_orders_2(X37,esk4_4(X36,X37,X38,X41),X41)|(~m1_subset_1(X41,u1_struct_0(X37))|X36!=X41)|r2_hidden(X36,a_2_0_orders_2(X37,X38))|(v2_struct_0(X37)|~v3_orders_2(X37)|~v4_orders_2(X37)|~v5_orders_2(X37)|~l1_orders_2(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.10/0.36  fof(c_0_23, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.10/0.36  cnf(c_0_24, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.10/0.36  cnf(c_0_25, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.10/0.36  cnf(c_0_26, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.10/0.36  cnf(c_0_27, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_28, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_29, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.10/0.36  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_21])).
% 0.10/0.36  cnf(c_0_33, plain, (r2_orders_2(X2,X1,esk3_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.10/0.36  cnf(c_0_34, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.10/0.36  cnf(c_0_35, plain, (X1=esk3_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.10/0.36  cnf(c_0_36, negated_conjecture, (k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.36  cnf(c_0_37, negated_conjecture, (k2_struct_0(esk5_0)=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.10/0.36  cnf(c_0_38, negated_conjecture, (k1_orders_2(esk5_0,X1)=a_2_0_orders_2(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_18])]), c_0_30])).
% 0.10/0.36  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.10/0.36  fof(c_0_40, plain, ![X33, X34]:(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|m1_subset_1(k1_orders_2(X33,X34),k1_zfmisc_1(u1_struct_0(X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).
% 0.10/0.36  cnf(c_0_41, plain, (v2_struct_0(X1)|r2_orders_2(X1,X2,esk3_3(X3,X1,X4))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,X4))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_33, c_0_34])).
% 0.10/0.36  cnf(c_0_42, negated_conjecture, (esk3_3(X1,esk5_0,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X1,a_2_0_orders_2(esk5_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_28]), c_0_29]), c_0_18])]), c_0_30])).
% 0.10/0.36  fof(c_0_43, plain, ![X23, X25, X26]:((r2_hidden(esk2_1(X23),X23)|X23=k1_xboole_0)&((~r2_hidden(X25,X23)|esk2_1(X23)!=k4_tarski(X25,X26)|X23=k1_xboole_0)&(~r2_hidden(X26,X23)|esk2_1(X23)!=k4_tarski(X25,X26)|X23=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.10/0.36  cnf(c_0_44, negated_conjecture, (k1_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.10/0.36  cnf(c_0_45, negated_conjecture, (k1_orders_2(esk5_0,u1_struct_0(esk5_0))=a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.10/0.36  fof(c_0_46, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.10/0.36  cnf(c_0_47, plain, (v2_struct_0(X1)|m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.10/0.36  cnf(c_0_48, negated_conjecture, (r2_orders_2(esk5_0,X1,esk3_3(X2,esk5_0,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X2,a_2_0_orders_2(esk5_0,X3))|~r2_hidden(X1,X3)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_27]), c_0_28]), c_0_29]), c_0_18])]), c_0_30])).
% 0.10/0.36  cnf(c_0_49, negated_conjecture, (esk3_3(X1,esk5_0,u1_struct_0(esk5_0))=X1|~r2_hidden(X1,a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 0.10/0.36  cnf(c_0_50, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.10/0.36  cnf(c_0_51, negated_conjecture, (a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.10/0.36  cnf(c_0_52, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.10/0.36  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.10/0.36  cnf(c_0_54, negated_conjecture, (m1_subset_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_27]), c_0_28]), c_0_29]), c_0_18]), c_0_39])]), c_0_30])).
% 0.10/0.36  fof(c_0_55, plain, ![X28, X29, X30]:(((r1_orders_2(X28,X29,X30)|~r2_orders_2(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))&(X29!=X30|~r2_orders_2(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28)))&(~r1_orders_2(X28,X29,X30)|X29=X30|r2_orders_2(X28,X29,X30)|~m1_subset_1(X30,u1_struct_0(X28))|~m1_subset_1(X29,u1_struct_0(X28))|~l1_orders_2(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.10/0.36  cnf(c_0_56, negated_conjecture, (r2_orders_2(esk5_0,X1,esk3_3(X2,esk5_0,u1_struct_0(esk5_0)))|~r2_hidden(X2,a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_48, c_0_39])).
% 0.10/0.36  cnf(c_0_57, negated_conjecture, (esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0))=esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.10/0.36  cnf(c_0_58, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_50])).
% 0.10/0.36  cnf(c_0_59, negated_conjecture, (r1_tarski(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.10/0.36  cnf(c_0_60, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.10/0.36  cnf(c_0_61, negated_conjecture, (r2_orders_2(esk5_0,X1,esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_50]), c_0_51]), c_0_57])).
% 0.10/0.36  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_51])).
% 0.10/0.36  cnf(c_0_63, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_34, c_0_54])).
% 0.10/0.36  cnf(c_0_64, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_60])).
% 0.10/0.36  cnf(c_0_65, negated_conjecture, (r2_orders_2(esk5_0,esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.10/0.36  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_50]), c_0_51])).
% 0.10/0.36  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_18]), c_0_66])]), ['proof']).
% 0.10/0.36  # SZS output end CNFRefutation
% 0.10/0.36  # Proof object total steps             : 68
% 0.10/0.36  # Proof object clause steps            : 43
% 0.10/0.36  # Proof object formula steps           : 25
% 0.10/0.36  # Proof object conjectures             : 28
% 0.10/0.36  # Proof object clause conjectures      : 25
% 0.10/0.36  # Proof object formula conjectures     : 3
% 0.10/0.36  # Proof object initial clauses used    : 19
% 0.10/0.36  # Proof object initial formulas used   : 12
% 0.10/0.36  # Proof object generating inferences   : 19
% 0.10/0.36  # Proof object simplifying inferences  : 35
% 0.10/0.36  # Training examples: 0 positive, 0 negative
% 0.10/0.36  # Parsed axioms                        : 15
% 0.10/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.36  # Initial clauses                      : 34
% 0.10/0.36  # Removed in clause preprocessing      : 0
% 0.10/0.36  # Initial clauses in saturation        : 34
% 0.10/0.36  # Processed clauses                    : 419
% 0.10/0.36  # ...of these trivial                  : 9
% 0.10/0.36  # ...subsumed                          : 95
% 0.10/0.36  # ...remaining for further processing  : 315
% 0.10/0.36  # Other redundant clauses eliminated   : 6
% 0.10/0.36  # Clauses deleted for lack of memory   : 0
% 0.10/0.36  # Backward-subsumed                    : 0
% 0.10/0.36  # Backward-rewritten                   : 2
% 0.10/0.36  # Generated clauses                    : 1107
% 0.10/0.36  # ...of the previous two non-trivial   : 1067
% 0.10/0.36  # Contextual simplify-reflections      : 1
% 0.10/0.36  # Paramodulations                      : 1101
% 0.10/0.36  # Factorizations                       : 0
% 0.10/0.36  # Equation resolutions                 : 6
% 0.10/0.36  # Propositional unsat checks           : 0
% 0.10/0.36  #    Propositional check models        : 0
% 0.10/0.36  #    Propositional check unsatisfiable : 0
% 0.10/0.36  #    Propositional clauses             : 0
% 0.10/0.36  #    Propositional clauses after purity: 0
% 0.10/0.36  #    Propositional unsat core size     : 0
% 0.10/0.36  #    Propositional preprocessing time  : 0.000
% 0.10/0.36  #    Propositional encoding time       : 0.000
% 0.10/0.36  #    Propositional solver time         : 0.000
% 0.10/0.36  #    Success case prop preproc time    : 0.000
% 0.10/0.36  #    Success case prop encoding time   : 0.000
% 0.10/0.36  #    Success case prop solver time     : 0.000
% 0.10/0.36  # Current number of processed clauses  : 274
% 0.10/0.36  #    Positive orientable unit clauses  : 37
% 0.10/0.36  #    Positive unorientable unit clauses: 0
% 0.10/0.36  #    Negative unit clauses             : 3
% 0.10/0.36  #    Non-unit-clauses                  : 234
% 0.10/0.36  # Current number of unprocessed clauses: 714
% 0.10/0.36  # ...number of literals in the above   : 2022
% 0.10/0.36  # Current number of archived formulas  : 0
% 0.10/0.36  # Current number of archived clauses   : 35
% 0.10/0.36  # Clause-clause subsumption calls (NU) : 8091
% 0.10/0.36  # Rec. Clause-clause subsumption calls : 4556
% 0.10/0.36  # Non-unit clause-clause subsumptions  : 96
% 0.10/0.36  # Unit Clause-clause subsumption calls : 109
% 0.10/0.36  # Rewrite failures with RHS unbound    : 0
% 0.10/0.36  # BW rewrite match attempts            : 41
% 0.10/0.36  # BW rewrite match successes           : 2
% 0.10/0.36  # Condensation attempts                : 0
% 0.10/0.36  # Condensation successes               : 0
% 0.10/0.36  # Termbank termtop insertions          : 32632
% 0.10/0.36  
% 0.10/0.36  # -------------------------------------------------
% 0.10/0.36  # User time                : 0.043 s
% 0.10/0.36  # System time              : 0.004 s
% 0.10/0.36  # Total time               : 0.047 s
% 0.10/0.36  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

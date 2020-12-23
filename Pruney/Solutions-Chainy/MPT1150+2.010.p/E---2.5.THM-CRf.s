%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:35 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 126 expanded)
%              Number of clauses        :   36 (  50 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  319 ( 696 expanded)
%              Number of equality atoms :   34 (  83 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   56 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t44_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

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

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_11,plain,(
    ! [X27,X28,X29] :
      ( ( r1_orders_2(X27,X28,X29)
        | ~ r2_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( X28 != X29
        | ~ r2_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,X28,X29)
        | X28 = X29
        | r2_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_12,plain,(
    ! [X35,X36,X37,X39,X40] :
      ( ( m1_subset_1(esk3_3(X35,X36,X37),u1_struct_0(X36))
        | ~ r2_hidden(X35,a_2_0_orders_2(X36,X37))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) )
      & ( X35 = esk3_3(X35,X36,X37)
        | ~ r2_hidden(X35,a_2_0_orders_2(X36,X37))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) )
      & ( ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ r2_hidden(X39,X37)
        | r2_orders_2(X36,X39,esk3_3(X35,X36,X37))
        | ~ r2_hidden(X35,a_2_0_orders_2(X36,X37))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) )
      & ( m1_subset_1(esk4_4(X35,X36,X37,X40),u1_struct_0(X36))
        | ~ m1_subset_1(X40,u1_struct_0(X36))
        | X35 != X40
        | r2_hidden(X35,a_2_0_orders_2(X36,X37))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) )
      & ( r2_hidden(esk4_4(X35,X36,X37,X40),X37)
        | ~ m1_subset_1(X40,u1_struct_0(X36))
        | X35 != X40
        | r2_hidden(X35,a_2_0_orders_2(X36,X37))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) )
      & ( ~ r2_orders_2(X36,esk4_4(X35,X36,X37,X40),X40)
        | ~ m1_subset_1(X40,u1_struct_0(X36))
        | X35 != X40
        | r2_hidden(X35,a_2_0_orders_2(X36,X37))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

fof(c_0_13,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_orders_2])).

cnf(c_0_17,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ v3_orders_2(X32)
      | ~ v4_orders_2(X32)
      | ~ v5_orders_2(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | m1_subset_1(k1_orders_2(X32,X33),k1_zfmisc_1(u1_struct_0(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_24,plain,(
    ! [X26] :
      ( ~ l1_struct_0(X26)
      | k2_struct_0(X26) = u1_struct_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | r2_orders_2(X1,X2,esk3_3(X3,X1,X4))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v3_orders_2(X30)
      | ~ v4_orders_2(X30)
      | ~ v5_orders_2(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | k1_orders_2(X30,X31) = a_2_0_orders_2(X30,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

cnf(c_0_32,negated_conjecture,
    ( k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk3_3(X3,X1,X2),X2)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_19])).

cnf(c_0_37,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_38,plain,(
    ! [X21,X23,X24,X25] :
      ( ( r2_hidden(esk2_1(X21),X21)
        | X21 = k1_xboole_0 )
      & ( ~ r2_hidden(X23,X21)
        | esk2_1(X21) != k3_mcart_1(X23,X24,X25)
        | X21 = k1_xboole_0 )
      & ( ~ r2_hidden(X24,X21)
        | esk2_1(X21) != k3_mcart_1(X23,X24,X25)
        | X21 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_orders_2(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k1_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_48,plain,(
    ! [X34] :
      ( ~ l1_orders_2(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_53,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( a_2_0_orders_2(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(esk2_1(a_2_0_orders_2(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( a_2_0_orders_2(X1,X2) = k1_xboole_0
    | v2_struct_0(X1)
    | r2_hidden(esk2_1(a_2_0_orders_2(X1,X2)),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45])])).

cnf(c_0_57,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_46])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.59/0.77  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.59/0.77  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.59/0.77  #
% 0.59/0.77  # Preprocessing time       : 0.028 s
% 0.59/0.77  
% 0.59/0.77  # Proof found!
% 0.59/0.77  # SZS status Theorem
% 0.59/0.77  # SZS output start CNFRefutation
% 0.59/0.77  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 0.59/0.77  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.59/0.77  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.59/0.77  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.59/0.77  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.59/0.77  fof(t44_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 0.59/0.77  fof(dt_k1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 0.59/0.77  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.59/0.77  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 0.59/0.77  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.59/0.77  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.59/0.77  fof(c_0_11, plain, ![X27, X28, X29]:(((r1_orders_2(X27,X28,X29)|~r2_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))&(X28!=X29|~r2_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27)))&(~r1_orders_2(X27,X28,X29)|X28=X29|r2_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.59/0.77  fof(c_0_12, plain, ![X35, X36, X37, X39, X40]:((((m1_subset_1(esk3_3(X35,X36,X37),u1_struct_0(X36))|~r2_hidden(X35,a_2_0_orders_2(X36,X37))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))))&(X35=esk3_3(X35,X36,X37)|~r2_hidden(X35,a_2_0_orders_2(X36,X37))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))))))&(~m1_subset_1(X39,u1_struct_0(X36))|(~r2_hidden(X39,X37)|r2_orders_2(X36,X39,esk3_3(X35,X36,X37)))|~r2_hidden(X35,a_2_0_orders_2(X36,X37))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36))))))&((m1_subset_1(esk4_4(X35,X36,X37,X40),u1_struct_0(X36))|(~m1_subset_1(X40,u1_struct_0(X36))|X35!=X40)|r2_hidden(X35,a_2_0_orders_2(X36,X37))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))))&((r2_hidden(esk4_4(X35,X36,X37,X40),X37)|(~m1_subset_1(X40,u1_struct_0(X36))|X35!=X40)|r2_hidden(X35,a_2_0_orders_2(X36,X37))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))))&(~r2_orders_2(X36,esk4_4(X35,X36,X37,X40),X40)|(~m1_subset_1(X40,u1_struct_0(X36))|X35!=X40)|r2_hidden(X35,a_2_0_orders_2(X36,X37))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.59/0.77  fof(c_0_13, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.59/0.77  fof(c_0_14, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.59/0.77  fof(c_0_15, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.59/0.77  fof(c_0_16, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t44_orders_2])).
% 0.59/0.77  cnf(c_0_17, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.59/0.77  cnf(c_0_18, plain, (r2_orders_2(X2,X1,esk3_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.59/0.77  cnf(c_0_19, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.59/0.77  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.59/0.77  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.59/0.77  fof(c_0_22, plain, ![X32, X33]:(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|m1_subset_1(k1_orders_2(X32,X33),k1_zfmisc_1(u1_struct_0(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).
% 0.59/0.77  fof(c_0_23, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.59/0.77  fof(c_0_24, plain, ![X26]:(~l1_struct_0(X26)|k2_struct_0(X26)=u1_struct_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.59/0.77  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.59/0.77  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.59/0.77  cnf(c_0_27, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_17])).
% 0.59/0.77  cnf(c_0_28, plain, (v2_struct_0(X1)|r2_orders_2(X1,X2,esk3_3(X3,X1,X4))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,X4))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.59/0.77  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.59/0.77  cnf(c_0_30, plain, (v2_struct_0(X1)|m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.59/0.77  fof(c_0_31, plain, ![X30, X31]:(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|k1_orders_2(X30,X31)=a_2_0_orders_2(X30,X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.59/0.77  cnf(c_0_32, negated_conjecture, (k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.77  cnf(c_0_33, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.59/0.77  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.59/0.77  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.59/0.77  cnf(c_0_36, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk3_3(X3,X1,X2),X2)|~r2_hidden(X3,a_2_0_orders_2(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_19])).
% 0.59/0.77  cnf(c_0_37, plain, (X1=esk3_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.59/0.77  fof(c_0_38, plain, ![X21, X23, X24, X25]:((r2_hidden(esk2_1(X21),X21)|X21=k1_xboole_0)&((~r2_hidden(X23,X21)|esk2_1(X21)!=k3_mcart_1(X23,X24,X25)|X21=k1_xboole_0)&(~r2_hidden(X24,X21)|esk2_1(X21)!=k3_mcart_1(X23,X24,X25)|X21=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.59/0.77  cnf(c_0_39, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k1_orders_2(X1,X3))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.59/0.77  cnf(c_0_40, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.59/0.77  cnf(c_0_41, negated_conjecture, (k1_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.59/0.77  cnf(c_0_42, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.77  cnf(c_0_43, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.77  cnf(c_0_44, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.77  cnf(c_0_45, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.77  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.59/0.77  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.59/0.77  fof(c_0_48, plain, ![X34]:(~l1_orders_2(X34)|l1_struct_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.59/0.77  cnf(c_0_49, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,X2))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.59/0.77  cnf(c_0_50, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.59/0.77  cnf(c_0_51, plain, (v2_struct_0(X1)|r2_hidden(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_0_orders_2(X1,X3))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.59/0.77  cnf(c_0_52, negated_conjecture, (a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])]), c_0_47])).
% 0.59/0.77  cnf(c_0_53, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.59/0.77  cnf(c_0_54, plain, (a_2_0_orders_2(X1,X2)=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(esk2_1(a_2_0_orders_2(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.59/0.77  cnf(c_0_55, plain, (a_2_0_orders_2(X1,X2)=k1_xboole_0|v2_struct_0(X1)|r2_hidden(esk2_1(a_2_0_orders_2(X1,X2)),u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 0.59/0.77  cnf(c_0_56, negated_conjecture, (a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45])])).
% 0.59/0.77  cnf(c_0_57, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_46])])).
% 0.59/0.77  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_42]), c_0_43]), c_0_44]), c_0_45])]), c_0_47]), ['proof']).
% 0.59/0.77  # SZS output end CNFRefutation
% 0.59/0.77  # Proof object total steps             : 59
% 0.59/0.77  # Proof object clause steps            : 36
% 0.59/0.77  # Proof object formula steps           : 23
% 0.59/0.77  # Proof object conjectures             : 13
% 0.59/0.77  # Proof object clause conjectures      : 10
% 0.59/0.77  # Proof object formula conjectures     : 3
% 0.59/0.77  # Proof object initial clauses used    : 20
% 0.59/0.77  # Proof object initial formulas used   : 11
% 0.59/0.77  # Proof object generating inferences   : 14
% 0.59/0.77  # Proof object simplifying inferences  : 20
% 0.59/0.77  # Training examples: 0 positive, 0 negative
% 0.59/0.77  # Parsed axioms                        : 14
% 0.59/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.77  # Initial clauses                      : 31
% 0.59/0.77  # Removed in clause preprocessing      : 0
% 0.59/0.77  # Initial clauses in saturation        : 31
% 0.59/0.77  # Processed clauses                    : 2791
% 0.59/0.77  # ...of these trivial                  : 0
% 0.59/0.77  # ...subsumed                          : 1928
% 0.59/0.77  # ...remaining for further processing  : 863
% 0.59/0.77  # Other redundant clauses eliminated   : 4
% 0.59/0.77  # Clauses deleted for lack of memory   : 0
% 0.59/0.77  # Backward-subsumed                    : 10
% 0.59/0.77  # Backward-rewritten                   : 0
% 0.59/0.77  # Generated clauses                    : 14103
% 0.59/0.77  # ...of the previous two non-trivial   : 12844
% 0.59/0.77  # Contextual simplify-reflections      : 17
% 0.59/0.77  # Paramodulations                      : 14099
% 0.59/0.77  # Factorizations                       : 0
% 0.59/0.77  # Equation resolutions                 : 4
% 0.59/0.77  # Propositional unsat checks           : 0
% 0.59/0.77  #    Propositional check models        : 0
% 0.59/0.77  #    Propositional check unsatisfiable : 0
% 0.59/0.77  #    Propositional clauses             : 0
% 0.59/0.77  #    Propositional clauses after purity: 0
% 0.59/0.77  #    Propositional unsat core size     : 0
% 0.59/0.77  #    Propositional preprocessing time  : 0.000
% 0.59/0.77  #    Propositional encoding time       : 0.000
% 0.59/0.77  #    Propositional solver time         : 0.000
% 0.59/0.77  #    Success case prop preproc time    : 0.000
% 0.59/0.77  #    Success case prop encoding time   : 0.000
% 0.59/0.77  #    Success case prop solver time     : 0.000
% 0.59/0.77  # Current number of processed clauses  : 849
% 0.59/0.77  #    Positive orientable unit clauses  : 8
% 0.59/0.77  #    Positive unorientable unit clauses: 0
% 0.59/0.77  #    Negative unit clauses             : 5
% 0.59/0.77  #    Non-unit-clauses                  : 836
% 0.59/0.77  # Current number of unprocessed clauses: 10080
% 0.59/0.77  # ...number of literals in the above   : 75804
% 0.59/0.77  # Current number of archived formulas  : 0
% 0.59/0.77  # Current number of archived clauses   : 10
% 0.59/0.77  # Clause-clause subsumption calls (NU) : 152678
% 0.59/0.77  # Rec. Clause-clause subsumption calls : 17448
% 0.59/0.77  # Non-unit clause-clause subsumptions  : 1604
% 0.59/0.77  # Unit Clause-clause subsumption calls : 11
% 0.59/0.77  # Rewrite failures with RHS unbound    : 0
% 0.59/0.77  # BW rewrite match attempts            : 5
% 0.59/0.77  # BW rewrite match successes           : 0
% 0.59/0.77  # Condensation attempts                : 0
% 0.59/0.77  # Condensation successes               : 0
% 0.59/0.77  # Termbank termtop insertions          : 425289
% 0.59/0.77  
% 0.59/0.77  # -------------------------------------------------
% 0.59/0.77  # User time                : 0.408 s
% 0.59/0.77  # System time              : 0.012 s
% 0.59/0.77  # Total time               : 0.420 s
% 0.59/0.77  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

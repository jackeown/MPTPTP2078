%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:36 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 (1588 expanded)
%              Number of clauses        :   77 ( 544 expanded)
%              Number of leaves         :   20 ( 400 expanded)
%              Depth                    :   17
%              Number of atoms          :  472 (7851 expanded)
%              Number of equality atoms :   52 (1172 expanded)
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

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t43_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k1_orders_2(X1,k1_struct_0(X1)) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

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

fof(d2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k1_struct_0(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(t30_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r1_orders_2(X1,X2,X3)
                  & r2_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_orders_2])).

fof(c_0_21,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v3_orders_2(X30)
      | ~ v4_orders_2(X30)
      | ~ v5_orders_2(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | k1_orders_2(X30,X31) = a_2_0_orders_2(X30,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_22,plain,(
    ! [X29] :
      ( ~ l1_struct_0(X29)
      | m1_subset_1(k2_struct_0(X29),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_23,plain,(
    ! [X32] :
      ( ~ l1_orders_2(X32)
      | l1_struct_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_24,plain,(
    ! [X49] :
      ( v2_struct_0(X49)
      | ~ v3_orders_2(X49)
      | ~ v4_orders_2(X49)
      | ~ v5_orders_2(X49)
      | ~ l1_orders_2(X49)
      | k1_orders_2(X49,k1_struct_0(X49)) = u1_struct_0(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_orders_2])])])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_26,plain,(
    ! [X33,X34,X35,X37,X38] :
      ( ( m1_subset_1(esk3_3(X33,X34,X35),u1_struct_0(X34))
        | ~ r2_hidden(X33,a_2_0_orders_2(X34,X35))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( X33 = esk3_3(X33,X34,X35)
        | ~ r2_hidden(X33,a_2_0_orders_2(X34,X35))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( ~ m1_subset_1(X37,u1_struct_0(X34))
        | ~ r2_hidden(X37,X35)
        | r2_orders_2(X34,X37,esk3_3(X33,X34,X35))
        | ~ r2_hidden(X33,a_2_0_orders_2(X34,X35))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( m1_subset_1(esk4_4(X33,X34,X35,X38),u1_struct_0(X34))
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | X33 != X38
        | r2_hidden(X33,a_2_0_orders_2(X34,X35))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( r2_hidden(esk4_4(X33,X34,X35,X38),X35)
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | X33 != X38
        | r2_hidden(X33,a_2_0_orders_2(X34,X35))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) )
      & ( ~ r2_orders_2(X34,esk4_4(X33,X34,X35,X38),X38)
        | ~ m1_subset_1(X38,u1_struct_0(X34))
        | X33 != X38
        | r2_hidden(X33,a_2_0_orders_2(X34,X35))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v4_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,k1_struct_0(X1)) = u1_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X27] :
      ( ~ l1_struct_0(X27)
      | k1_struct_0(X27) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).

cnf(c_0_37,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
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

cnf(c_0_39,plain,
    ( k1_orders_2(X1,k2_struct_0(X1)) = a_2_0_orders_2(X1,k2_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_40,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | ~ r1_tarski(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_41,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_42,negated_conjecture,
    ( k1_orders_2(esk5_0,k1_struct_0(esk5_0)) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_43,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_45,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_46,plain,
    ( esk3_3(X1,X2,k2_struct_0(X2)) = X1
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,k2_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_29])).

cnf(c_0_47,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( k1_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( k1_orders_2(esk5_0,k2_struct_0(esk5_0)) = a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_50,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( k1_orders_2(esk5_0,k1_xboole_0) = u1_struct_0(esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_56,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_58,plain,
    ( esk3_3(esk2_1(a_2_0_orders_2(X1,k2_struct_0(X1))),X1,k2_struct_0(X1)) = esk2_1(a_2_0_orders_2(X1,k2_struct_0(X1)))
    | a_2_0_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk4_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,k1_xboole_0) = u1_struct_0(esk5_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_53]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_54])]),c_0_35])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ r2_hidden(X1,k2_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_28])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_65,plain,(
    ! [X14] : m1_subset_1(k2_subset_1(X14),k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_66,plain,(
    ! [X13] : k2_subset_1(X13) = X13 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_3(X2,X1,k2_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,k2_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_29])).

cnf(c_0_68,negated_conjecture,
    ( esk3_3(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),esk5_0,k2_struct_0(esk5_0)) = esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_59]),c_0_35])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_0_orders_2(X1,k1_xboole_0))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_54]),c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,k1_xboole_0) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_29]),c_0_31])])).

cnf(c_0_71,plain,
    ( m1_subset_1(esk1_2(k2_struct_0(X1),X2),u1_struct_0(X1))
    | r1_tarski(k2_struct_0(X1),X2)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_73,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),u1_struct_0(esk5_0))
    | ~ r2_hidden(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_78,plain,
    ( m1_subset_1(esk1_2(k2_struct_0(X1),X2),u1_struct_0(X1))
    | r1_tarski(k2_struct_0(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_29])).

cnf(c_0_79,plain,
    ( r2_orders_2(X1,X2,esk3_3(X3,X1,X4))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_72,c_0_55])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_47]),c_0_59])).

fof(c_0_82,plain,(
    ! [X28] :
      ( ~ l1_struct_0(X28)
      | k2_struct_0(X28) = u1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_83,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_2(X1,u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk1_2(k2_struct_0(esk5_0),X1),u1_struct_0(esk5_0))
    | r1_tarski(k2_struct_0(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_31])).

cnf(c_0_86,plain,
    ( r2_orders_2(X1,X2,esk3_3(X3,X1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_81]),c_0_70]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_88,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_89,plain,(
    ! [X40,X41,X42] :
      ( ( ~ r3_orders_2(X40,X41,X42)
        | r1_orders_2(X40,X41,X42)
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | ~ m1_subset_1(X42,u1_struct_0(X40)) )
      & ( ~ r1_orders_2(X40,X41,X42)
        | r3_orders_2(X40,X41,X42)
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | ~ m1_subset_1(X42,u1_struct_0(X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_3(X2,X1,k1_xboole_0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_91,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

fof(c_0_93,plain,(
    ! [X46,X47,X48] :
      ( ~ v5_orders_2(X46)
      | ~ l1_orders_2(X46)
      | ~ m1_subset_1(X47,u1_struct_0(X46))
      | ~ m1_subset_1(X48,u1_struct_0(X46))
      | ~ r1_orders_2(X46,X47,X48)
      | ~ r2_orders_2(X46,X48,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_orders_2])])])).

cnf(c_0_94,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | r2_orders_2(X1,X2,esk3_3(esk2_1(a_2_0_orders_2(X1,u1_struct_0(X1))),X1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_47])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),u1_struct_0(esk5_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)) != k1_xboole_0
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_88])).

cnf(c_0_97,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk3_3(X1,esk5_0,k1_xboole_0),u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_70]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_99,plain,
    ( esk3_3(X1,X2,k1_xboole_0) = X1
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_54])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_101,plain,
    ( ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_102,negated_conjecture,
    ( r2_orders_2(esk5_0,esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)))
    | ~ l1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),u1_struct_0(esk5_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_88])).

cnf(c_0_104,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,esk3_3(X2,esk5_0,k1_xboole_0))
    | ~ r3_orders_2(esk5_0,X1,esk3_3(X2,esk5_0,k1_xboole_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_31]),c_0_34])]),c_0_35])).

cnf(c_0_105,negated_conjecture,
    ( esk3_3(X1,esk5_0,k1_xboole_0) = X1
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_70]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_106,negated_conjecture,
    ( esk3_3(X1,esk5_0,k2_struct_0(esk5_0)) = X1
    | ~ r2_hidden(X1,a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_100]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_107,negated_conjecture,
    ( ~ r1_orders_2(esk5_0,esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)),esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))
    | ~ l1_struct_0(esk5_0)
    | ~ m1_subset_1(esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_31]),c_0_32])]),c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( r1_orders_2(esk5_0,X1,X2)
    | ~ r3_orders_2(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( esk3_3(X1,esk5_0,u1_struct_0(esk5_0)) = X1
    | ~ l1_struct_0(esk5_0)
    | ~ r2_hidden(X1,a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_88])).

fof(c_0_110,plain,(
    ! [X43,X44,X45] :
      ( v2_struct_0(X43)
      | ~ v3_orders_2(X43)
      | ~ l1_orders_2(X43)
      | ~ m1_subset_1(X44,u1_struct_0(X43))
      | ~ m1_subset_1(X45,u1_struct_0(X43))
      | r3_orders_2(X43,X44,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_111,negated_conjecture,
    ( ~ r3_orders_2(esk5_0,esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)),esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))
    | ~ l1_struct_0(esk5_0)
    | ~ m1_subset_1(esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_95])).

cnf(c_0_112,negated_conjecture,
    ( esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)) = esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))
    | ~ l1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_47]),c_0_96])).

cnf(c_0_113,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( ~ r3_orders_2(esk5_0,esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))
    | ~ l1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_103])).

cnf(c_0_115,negated_conjecture,
    ( r3_orders_2(esk5_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_81]),c_0_31]),c_0_34])]),c_0_35])).

cnf(c_0_116,negated_conjecture,
    ( ~ l1_struct_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_103])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_29]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:46:05 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.50  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.21/0.50  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.50  #
% 0.21/0.50  # Preprocessing time       : 0.029 s
% 0.21/0.50  
% 0.21/0.50  # Proof found!
% 0.21/0.50  # SZS status Theorem
% 0.21/0.50  # SZS output start CNFRefutation
% 0.21/0.50  fof(t44_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 0.21/0.50  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 0.21/0.50  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.21/0.50  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.21/0.50  fof(t43_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k1_struct_0(X1))=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_orders_2)).
% 0.21/0.50  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.21/0.50  fof(d2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k1_struct_0(X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 0.21/0.50  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.21/0.50  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.50  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.50  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.50  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.50  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.21/0.50  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.21/0.50  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.50  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.21/0.50  fof(t30_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 0.21/0.50  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.21/0.50  fof(c_0_20, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t44_orders_2])).
% 0.21/0.50  fof(c_0_21, plain, ![X30, X31]:(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|k1_orders_2(X30,X31)=a_2_0_orders_2(X30,X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.21/0.50  fof(c_0_22, plain, ![X29]:(~l1_struct_0(X29)|m1_subset_1(k2_struct_0(X29),k1_zfmisc_1(u1_struct_0(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.21/0.50  fof(c_0_23, plain, ![X32]:(~l1_orders_2(X32)|l1_struct_0(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.21/0.50  fof(c_0_24, plain, ![X49]:(v2_struct_0(X49)|~v3_orders_2(X49)|~v4_orders_2(X49)|~v5_orders_2(X49)|~l1_orders_2(X49)|k1_orders_2(X49,k1_struct_0(X49))=u1_struct_0(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_orders_2])])])).
% 0.21/0.50  fof(c_0_25, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.21/0.50  fof(c_0_26, plain, ![X33, X34, X35, X37, X38]:((((m1_subset_1(esk3_3(X33,X34,X35),u1_struct_0(X34))|~r2_hidden(X33,a_2_0_orders_2(X34,X35))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))))&(X33=esk3_3(X33,X34,X35)|~r2_hidden(X33,a_2_0_orders_2(X34,X35))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))))))&(~m1_subset_1(X37,u1_struct_0(X34))|(~r2_hidden(X37,X35)|r2_orders_2(X34,X37,esk3_3(X33,X34,X35)))|~r2_hidden(X33,a_2_0_orders_2(X34,X35))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))))))&((m1_subset_1(esk4_4(X33,X34,X35,X38),u1_struct_0(X34))|(~m1_subset_1(X38,u1_struct_0(X34))|X33!=X38)|r2_hidden(X33,a_2_0_orders_2(X34,X35))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))))&((r2_hidden(esk4_4(X33,X34,X35,X38),X35)|(~m1_subset_1(X38,u1_struct_0(X34))|X33!=X38)|r2_hidden(X33,a_2_0_orders_2(X34,X35))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))))&(~r2_orders_2(X34,esk4_4(X33,X34,X35,X38),X38)|(~m1_subset_1(X38,u1_struct_0(X34))|X33!=X38)|r2_hidden(X33,a_2_0_orders_2(X34,X35))|(v2_struct_0(X34)|~v3_orders_2(X34)|~v4_orders_2(X34)|~v5_orders_2(X34)|~l1_orders_2(X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.21/0.50  cnf(c_0_27, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.50  cnf(c_0_28, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.50  cnf(c_0_29, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.50  cnf(c_0_30, plain, (v2_struct_0(X1)|k1_orders_2(X1,k1_struct_0(X1))=u1_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.50  cnf(c_0_31, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.50  cnf(c_0_32, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.50  cnf(c_0_33, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.50  cnf(c_0_34, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.50  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.50  fof(c_0_36, plain, ![X27]:(~l1_struct_0(X27)|k1_struct_0(X27)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).
% 0.21/0.50  cnf(c_0_37, plain, (X1=esk3_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.50  fof(c_0_38, plain, ![X23, X25, X26]:((r2_hidden(esk2_1(X23),X23)|X23=k1_xboole_0)&((~r2_hidden(X25,X23)|esk2_1(X23)!=k4_tarski(X25,X26)|X23=k1_xboole_0)&(~r2_hidden(X26,X23)|esk2_1(X23)!=k4_tarski(X25,X26)|X23=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.21/0.50  cnf(c_0_39, plain, (k1_orders_2(X1,k2_struct_0(X1))=a_2_0_orders_2(X1,k2_struct_0(X1))|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.21/0.50  fof(c_0_40, plain, ![X21, X22]:(~r2_hidden(X21,X22)|~r1_tarski(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.50  fof(c_0_41, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.50  cnf(c_0_42, negated_conjecture, (k1_orders_2(esk5_0,k1_struct_0(esk5_0))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_43, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.50  fof(c_0_44, plain, ![X15]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.50  fof(c_0_45, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.50  cnf(c_0_46, plain, (esk3_3(X1,X2,k2_struct_0(X2))=X1|v2_struct_0(X2)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,k2_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_29])).
% 0.21/0.50  cnf(c_0_47, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.50  cnf(c_0_48, negated_conjecture, (k1_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.50  cnf(c_0_49, negated_conjecture, (k1_orders_2(esk5_0,k2_struct_0(esk5_0))=a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_50, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_0_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.50  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.50  cnf(c_0_52, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.50  cnf(c_0_53, negated_conjecture, (k1_orders_2(esk5_0,k1_xboole_0)=u1_struct_0(esk5_0)|~l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.50  cnf(c_0_54, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.50  cnf(c_0_55, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.50  fof(c_0_56, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.50  cnf(c_0_57, plain, (m1_subset_1(esk3_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.50  cnf(c_0_58, plain, (esk3_3(esk2_1(a_2_0_orders_2(X1,k2_struct_0(X1))),X1,k2_struct_0(X1))=esk2_1(a_2_0_orders_2(X1,k2_struct_0(X1)))|a_2_0_orders_2(X1,k2_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.50  cnf(c_0_59, negated_conjecture, (a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.21/0.50  cnf(c_0_60, plain, (v2_struct_0(X1)|r2_hidden(esk4_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_50])).
% 0.21/0.50  cnf(c_0_61, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.50  cnf(c_0_62, negated_conjecture, (a_2_0_orders_2(esk5_0,k1_xboole_0)=u1_struct_0(esk5_0)|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_53]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_54])]), c_0_35])).
% 0.21/0.50  cnf(c_0_63, plain, (m1_subset_1(X1,u1_struct_0(X2))|~l1_struct_0(X2)|~r2_hidden(X1,k2_struct_0(X2))), inference(spm,[status(thm)],[c_0_55, c_0_28])).
% 0.21/0.50  cnf(c_0_64, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.50  fof(c_0_65, plain, ![X14]:m1_subset_1(k2_subset_1(X14),k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.21/0.50  fof(c_0_66, plain, ![X13]:k2_subset_1(X13)=X13, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.21/0.50  cnf(c_0_67, plain, (v2_struct_0(X1)|m1_subset_1(esk3_3(X2,X1,k2_struct_0(X1)),u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r2_hidden(X2,a_2_0_orders_2(X1,k2_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_28]), c_0_29])).
% 0.21/0.50  cnf(c_0_68, negated_conjecture, (esk3_3(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),esk5_0,k2_struct_0(esk5_0))=esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_59]), c_0_35])).
% 0.21/0.50  cnf(c_0_69, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_0_orders_2(X1,k1_xboole_0))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_54]), c_0_61])).
% 0.21/0.50  cnf(c_0_70, negated_conjecture, (a_2_0_orders_2(esk5_0,k1_xboole_0)=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_29]), c_0_31])])).
% 0.21/0.50  cnf(c_0_71, plain, (m1_subset_1(esk1_2(k2_struct_0(X1),X2),u1_struct_0(X1))|r1_tarski(k2_struct_0(X1),X2)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.50  cnf(c_0_72, plain, (r2_orders_2(X2,X1,esk3_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.50  cnf(c_0_73, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.50  cnf(c_0_74, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.50  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),u1_struct_0(esk5_0))|~r2_hidden(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.50  cnf(c_0_77, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_78, plain, (m1_subset_1(esk1_2(k2_struct_0(X1),X2),u1_struct_0(X1))|r1_tarski(k2_struct_0(X1),X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_71, c_0_29])).
% 0.21/0.50  cnf(c_0_79, plain, (r2_orders_2(X1,X2,esk3_3(X3,X1,X4))|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,X4))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_72, c_0_55])).
% 0.21/0.50  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.50  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_47]), c_0_59])).
% 0.21/0.50  fof(c_0_82, plain, ![X28]:(~l1_struct_0(X28)|k2_struct_0(X28)=u1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.50  fof(c_0_83, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.50  cnf(c_0_84, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk5_0))|~m1_subset_1(esk1_2(X1,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.50  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk1_2(k2_struct_0(esk5_0),X1),u1_struct_0(esk5_0))|r1_tarski(k2_struct_0(esk5_0),X1)), inference(spm,[status(thm)],[c_0_78, c_0_31])).
% 0.21/0.50  cnf(c_0_86, plain, (r2_orders_2(X1,X2,esk3_3(X3,X1,u1_struct_0(X1)))|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r2_hidden(X3,a_2_0_orders_2(X1,u1_struct_0(X1)))|~r2_hidden(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.21/0.50  cnf(c_0_87, negated_conjecture, (r2_hidden(esk2_1(a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0))),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_81]), c_0_70]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_88, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.21/0.50  fof(c_0_89, plain, ![X40, X41, X42]:((~r3_orders_2(X40,X41,X42)|r1_orders_2(X40,X41,X42)|(v2_struct_0(X40)|~v3_orders_2(X40)|~l1_orders_2(X40)|~m1_subset_1(X41,u1_struct_0(X40))|~m1_subset_1(X42,u1_struct_0(X40))))&(~r1_orders_2(X40,X41,X42)|r3_orders_2(X40,X41,X42)|(v2_struct_0(X40)|~v3_orders_2(X40)|~l1_orders_2(X40)|~m1_subset_1(X41,u1_struct_0(X40))|~m1_subset_1(X42,u1_struct_0(X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.21/0.50  cnf(c_0_90, plain, (v2_struct_0(X1)|m1_subset_1(esk3_3(X2,X1,k1_xboole_0),u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r2_hidden(X2,a_2_0_orders_2(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_57, c_0_54])).
% 0.21/0.50  cnf(c_0_91, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.21/0.50  cnf(c_0_92, negated_conjecture, (r1_tarski(k2_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.21/0.50  fof(c_0_93, plain, ![X46, X47, X48]:(~v5_orders_2(X46)|~l1_orders_2(X46)|(~m1_subset_1(X47,u1_struct_0(X46))|(~m1_subset_1(X48,u1_struct_0(X46))|(~r1_orders_2(X46,X47,X48)|~r2_orders_2(X46,X48,X47))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_orders_2])])])).
% 0.21/0.50  cnf(c_0_94, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|r2_orders_2(X1,X2,esk3_3(esk2_1(a_2_0_orders_2(X1,u1_struct_0(X1))),X1,u1_struct_0(X1)))|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r2_hidden(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_86, c_0_47])).
% 0.21/0.50  cnf(c_0_95, negated_conjecture, (r2_hidden(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),u1_struct_0(esk5_0))|~l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.21/0.50  cnf(c_0_96, negated_conjecture, (a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))!=k1_xboole_0|~l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_88])).
% 0.21/0.50  cnf(c_0_97, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.21/0.50  cnf(c_0_98, negated_conjecture, (m1_subset_1(esk3_3(X1,esk5_0,k1_xboole_0),u1_struct_0(esk5_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_70]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_99, plain, (esk3_3(X1,X2,k1_xboole_0)=X1|v2_struct_0(X2)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_37, c_0_54])).
% 0.21/0.50  cnf(c_0_100, negated_conjecture, (m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.21/0.50  cnf(c_0_101, plain, (~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.21/0.50  cnf(c_0_102, negated_conjecture, (r2_orders_2(esk5_0,esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)))|~l1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35]), c_0_96])).
% 0.21/0.50  cnf(c_0_103, negated_conjecture, (m1_subset_1(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),u1_struct_0(esk5_0))|~l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_81, c_0_88])).
% 0.21/0.50  cnf(c_0_104, negated_conjecture, (r1_orders_2(esk5_0,X1,esk3_3(X2,esk5_0,k1_xboole_0))|~r3_orders_2(esk5_0,X1,esk3_3(X2,esk5_0,k1_xboole_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X2,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_31]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_105, negated_conjecture, (esk3_3(X1,esk5_0,k1_xboole_0)=X1|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_70]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_106, negated_conjecture, (esk3_3(X1,esk5_0,k2_struct_0(esk5_0))=X1|~r2_hidden(X1,a_2_0_orders_2(esk5_0,k2_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_100]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_107, negated_conjecture, (~r1_orders_2(esk5_0,esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)),esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))|~l1_struct_0(esk5_0)|~m1_subset_1(esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_31]), c_0_32])]), c_0_103])).
% 0.21/0.50  cnf(c_0_108, negated_conjecture, (r1_orders_2(esk5_0,X1,X2)|~r3_orders_2(esk5_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X2,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.21/0.50  cnf(c_0_109, negated_conjecture, (esk3_3(X1,esk5_0,u1_struct_0(esk5_0))=X1|~l1_struct_0(esk5_0)|~r2_hidden(X1,a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_106, c_0_88])).
% 0.21/0.50  fof(c_0_110, plain, ![X43, X44, X45]:(v2_struct_0(X43)|~v3_orders_2(X43)|~l1_orders_2(X43)|~m1_subset_1(X44,u1_struct_0(X43))|~m1_subset_1(X45,u1_struct_0(X43))|r3_orders_2(X43,X44,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.21/0.50  cnf(c_0_111, negated_conjecture, (~r3_orders_2(esk5_0,esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)),esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))|~l1_struct_0(esk5_0)|~m1_subset_1(esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_95])).
% 0.21/0.50  cnf(c_0_112, negated_conjecture, (esk3_3(esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk5_0,u1_struct_0(esk5_0))=esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0)))|~l1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_47]), c_0_96])).
% 0.21/0.50  cnf(c_0_113, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.21/0.50  cnf(c_0_114, negated_conjecture, (~r3_orders_2(esk5_0,esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))),esk2_1(a_2_0_orders_2(esk5_0,u1_struct_0(esk5_0))))|~l1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_103])).
% 0.21/0.50  cnf(c_0_115, negated_conjecture, (r3_orders_2(esk5_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_81]), c_0_31]), c_0_34])]), c_0_35])).
% 0.21/0.50  cnf(c_0_116, negated_conjecture, (~l1_struct_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_103])).
% 0.21/0.50  cnf(c_0_117, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_29]), c_0_31])]), ['proof']).
% 0.21/0.50  # SZS output end CNFRefutation
% 0.21/0.50  # Proof object total steps             : 118
% 0.21/0.50  # Proof object clause steps            : 77
% 0.21/0.50  # Proof object formula steps           : 41
% 0.21/0.50  # Proof object conjectures             : 41
% 0.21/0.50  # Proof object clause conjectures      : 38
% 0.21/0.50  # Proof object formula conjectures     : 3
% 0.21/0.50  # Proof object initial clauses used    : 29
% 0.21/0.50  # Proof object initial formulas used   : 20
% 0.21/0.50  # Proof object generating inferences   : 44
% 0.21/0.50  # Proof object simplifying inferences  : 96
% 0.21/0.50  # Training examples: 0 positive, 0 negative
% 0.21/0.50  # Parsed axioms                        : 20
% 0.21/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.50  # Initial clauses                      : 36
% 0.21/0.50  # Removed in clause preprocessing      : 1
% 0.21/0.50  # Initial clauses in saturation        : 35
% 0.21/0.50  # Processed clauses                    : 752
% 0.21/0.50  # ...of these trivial                  : 1
% 0.21/0.50  # ...subsumed                          : 316
% 0.21/0.50  # ...remaining for further processing  : 435
% 0.21/0.50  # Other redundant clauses eliminated   : 3
% 0.21/0.50  # Clauses deleted for lack of memory   : 0
% 0.21/0.50  # Backward-subsumed                    : 18
% 0.21/0.50  # Backward-rewritten                   : 4
% 0.21/0.50  # Generated clauses                    : 2119
% 0.21/0.50  # ...of the previous two non-trivial   : 2046
% 0.21/0.50  # Contextual simplify-reflections      : 19
% 0.21/0.50  # Paramodulations                      : 2110
% 0.21/0.50  # Factorizations                       : 6
% 0.21/0.50  # Equation resolutions                 : 3
% 0.21/0.50  # Propositional unsat checks           : 0
% 0.21/0.50  #    Propositional check models        : 0
% 0.21/0.50  #    Propositional check unsatisfiable : 0
% 0.21/0.50  #    Propositional clauses             : 0
% 0.21/0.50  #    Propositional clauses after purity: 0
% 0.21/0.50  #    Propositional unsat core size     : 0
% 0.21/0.50  #    Propositional preprocessing time  : 0.000
% 0.21/0.50  #    Propositional encoding time       : 0.000
% 0.21/0.50  #    Propositional solver time         : 0.000
% 0.21/0.50  #    Success case prop preproc time    : 0.000
% 0.21/0.50  #    Success case prop encoding time   : 0.000
% 0.21/0.50  #    Success case prop solver time     : 0.000
% 0.21/0.50  # Current number of processed clauses  : 410
% 0.21/0.50  #    Positive orientable unit clauses  : 18
% 0.21/0.50  #    Positive unorientable unit clauses: 0
% 0.21/0.50  #    Negative unit clauses             : 11
% 0.21/0.50  #    Non-unit-clauses                  : 381
% 0.21/0.50  # Current number of unprocessed clauses: 1311
% 0.21/0.50  # ...number of literals in the above   : 7042
% 0.21/0.50  # Current number of archived formulas  : 0
% 0.21/0.50  # Current number of archived clauses   : 23
% 0.21/0.50  # Clause-clause subsumption calls (NU) : 31627
% 0.21/0.50  # Rec. Clause-clause subsumption calls : 6524
% 0.21/0.50  # Non-unit clause-clause subsumptions  : 324
% 0.21/0.50  # Unit Clause-clause subsumption calls : 453
% 0.21/0.50  # Rewrite failures with RHS unbound    : 0
% 0.21/0.50  # BW rewrite match attempts            : 10
% 0.21/0.50  # BW rewrite match successes           : 5
% 0.21/0.50  # Condensation attempts                : 0
% 0.21/0.50  # Condensation successes               : 0
% 0.21/0.50  # Termbank termtop insertions          : 62605
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.134 s
% 0.21/0.50  # System time              : 0.009 s
% 0.21/0.50  # Total time               : 0.143 s
% 0.21/0.50  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------

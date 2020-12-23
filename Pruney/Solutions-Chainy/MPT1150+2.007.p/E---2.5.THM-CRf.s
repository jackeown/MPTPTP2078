%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:34 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 270 expanded)
%              Number of clauses        :   46 (  97 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  332 (1358 expanded)
%              Number of equality atoms :   51 ( 210 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t43_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => k1_orders_2(X1,k1_struct_0(X1)) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(d2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k1_struct_0(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => k1_orders_2(X1,k2_struct_0(X1)) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_orders_2])).

fof(c_0_16,plain,(
    ! [X8] : m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_17,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_18,plain,(
    ! [X35] :
      ( v2_struct_0(X35)
      | ~ v3_orders_2(X35)
      | ~ v4_orders_2(X35)
      | ~ v5_orders_2(X35)
      | ~ l1_orders_2(X35)
      | k1_orders_2(X35,k1_struct_0(X35)) = u1_struct_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_orders_2])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & k1_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_20,plain,(
    ! [X28,X29,X30,X32,X33] :
      ( ( m1_subset_1(esk2_3(X28,X29,X30),u1_struct_0(X29))
        | ~ r2_hidden(X28,a_2_0_orders_2(X29,X30))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( X28 = esk2_3(X28,X29,X30)
        | ~ r2_hidden(X28,a_2_0_orders_2(X29,X30))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X29))
        | ~ r2_hidden(X32,X30)
        | r2_orders_2(X29,X32,esk2_3(X28,X29,X30))
        | ~ r2_hidden(X28,a_2_0_orders_2(X29,X30))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( m1_subset_1(esk3_4(X28,X29,X30,X33),u1_struct_0(X29))
        | ~ m1_subset_1(X33,u1_struct_0(X29))
        | X28 != X33
        | r2_hidden(X28,a_2_0_orders_2(X29,X30))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( r2_hidden(esk3_4(X28,X29,X30,X33),X30)
        | ~ m1_subset_1(X33,u1_struct_0(X29))
        | X28 != X33
        | r2_hidden(X28,a_2_0_orders_2(X29,X30))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( ~ r2_orders_2(X29,esk3_4(X28,X29,X30,X33),X33)
        | ~ m1_subset_1(X33,u1_struct_0(X29))
        | X28 != X33
        | r2_hidden(X28,a_2_0_orders_2(X29,X30))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,k1_struct_0(X1)) = u1_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X20] :
      ( ~ l1_struct_0(X20)
      | k1_struct_0(X20) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).

fof(c_0_30,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | ~ r1_tarski(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_32,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_35,plain,(
    ! [X15,X17,X18,X19] :
      ( ( r2_hidden(esk1_1(X15),X15)
        | X15 = k1_xboole_0 )
      & ( ~ r2_hidden(X17,X15)
        | esk1_1(X15) != k3_mcart_1(X17,X18,X19)
        | X15 = k1_xboole_0 )
      & ( ~ r2_hidden(X18,X15)
        | esk1_1(X15) != k3_mcart_1(X17,X18,X19)
        | X15 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_36,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v3_orders_2(X25)
      | ~ v4_orders_2(X25)
      | ~ v5_orders_2(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | k1_orders_2(X25,X26) = a_2_0_orders_2(X25,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

cnf(c_0_37,negated_conjecture,
    ( k1_orders_2(esk4_0,k1_struct_0(esk4_0)) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_38,plain,
    ( k1_struct_0(X1) = k1_xboole_0
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk2_3(X2,X1,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,a_2_0_orders_2(X1,u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( k1_orders_2(esk4_0,k1_xboole_0) = u1_struct_0(esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_50,plain,(
    ! [X27] :
      ( ~ l1_orders_2(X27)
      | l1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r2_orders_2(X1,X2,esk2_3(X3,X1,X4))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | m1_subset_1(esk2_3(esk1_1(a_2_0_orders_2(X1,u1_struct_0(X1))),X1,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,k1_xboole_0) = u1_struct_0(esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_49])]),c_0_28])).

cnf(c_0_56,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_57,plain,(
    ! [X21] :
      ( ~ l1_struct_0(X21)
      | k2_struct_0(X21) = u1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_58,plain,(
    ! [X22,X23,X24] :
      ( ( r1_orders_2(X22,X23,X24)
        | ~ r2_orders_2(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( X23 != X24
        | ~ r2_orders_2(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X23,X24)
        | X23 = X24
        | r2_orders_2(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | r2_orders_2(X1,X2,esk2_3(X3,X1,u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_34])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_0_orders_2(X1,k1_xboole_0))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) = k1_xboole_0
    | m1_subset_1(esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,k1_xboole_0) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_27])])).

cnf(c_0_63,negated_conjecture,
    ( k1_orders_2(esk4_0,k2_struct_0(esk4_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k1_orders_2(X1,u1_struct_0(X1)) = a_2_0_orders_2(X1,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_66,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( a_2_0_orders_2(X1,u1_struct_0(X1)) = k1_xboole_0
    | v2_struct_0(X1)
    | r2_orders_2(X1,X2,esk2_3(esk1_1(a_2_0_orders_2(X1,u1_struct_0(X1))),X1,u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_68,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) = k1_xboole_0
    | r2_hidden(esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( k1_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k1_orders_2(esk4_0,u1_struct_0(esk4_0)) = a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_71,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) = k1_xboole_0
    | r2_orders_2(esk4_0,esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)),esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_24]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_73,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) != k1_xboole_0
    | ~ l1_struct_0(esk4_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_27])]),c_0_61])).

cnf(c_0_75,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_56]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.043 s
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t44_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_orders_2)).
% 0.20/0.41  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.41  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.41  fof(t43_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k1_struct_0(X1))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_orders_2)).
% 0.20/0.41  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.20/0.41  fof(d2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k1_struct_0(X1)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 0.20/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.41  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.20/0.41  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 0.20/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.41  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.41  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.41  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 0.20/0.41  fof(c_0_15, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>k1_orders_2(X1,k2_struct_0(X1))=k1_xboole_0)), inference(assume_negation,[status(cth)],[t44_orders_2])).
% 0.20/0.41  fof(c_0_16, plain, ![X8]:m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.41  fof(c_0_17, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.41  fof(c_0_18, plain, ![X35]:(v2_struct_0(X35)|~v3_orders_2(X35)|~v4_orders_2(X35)|~v5_orders_2(X35)|~l1_orders_2(X35)|k1_orders_2(X35,k1_struct_0(X35))=u1_struct_0(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_orders_2])])])).
% 0.20/0.41  fof(c_0_19, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&k1_orders_2(esk4_0,k2_struct_0(esk4_0))!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.41  fof(c_0_20, plain, ![X28, X29, X30, X32, X33]:((((m1_subset_1(esk2_3(X28,X29,X30),u1_struct_0(X29))|~r2_hidden(X28,a_2_0_orders_2(X29,X30))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))))&(X28=esk2_3(X28,X29,X30)|~r2_hidden(X28,a_2_0_orders_2(X29,X30))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))))&(~m1_subset_1(X32,u1_struct_0(X29))|(~r2_hidden(X32,X30)|r2_orders_2(X29,X32,esk2_3(X28,X29,X30)))|~r2_hidden(X28,a_2_0_orders_2(X29,X30))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))))))&((m1_subset_1(esk3_4(X28,X29,X30,X33),u1_struct_0(X29))|(~m1_subset_1(X33,u1_struct_0(X29))|X28!=X33)|r2_hidden(X28,a_2_0_orders_2(X29,X30))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))))&((r2_hidden(esk3_4(X28,X29,X30,X33),X30)|(~m1_subset_1(X33,u1_struct_0(X29))|X28!=X33)|r2_hidden(X28,a_2_0_orders_2(X29,X30))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))))&(~r2_orders_2(X29,esk3_4(X28,X29,X30,X33),X33)|(~m1_subset_1(X33,u1_struct_0(X29))|X28!=X33)|r2_hidden(X28,a_2_0_orders_2(X29,X30))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.20/0.41  cnf(c_0_21, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_22, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_23, plain, (v2_struct_0(X1)|k1_orders_2(X1,k1_struct_0(X1))=u1_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  fof(c_0_29, plain, ![X20]:(~l1_struct_0(X20)|k1_struct_0(X20)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_struct_0])])).
% 0.20/0.41  fof(c_0_30, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.41  fof(c_0_31, plain, ![X13, X14]:(~r2_hidden(X13,X14)|~r1_tarski(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.41  fof(c_0_32, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.41  cnf(c_0_33, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  fof(c_0_35, plain, ![X15, X17, X18, X19]:((r2_hidden(esk1_1(X15),X15)|X15=k1_xboole_0)&((~r2_hidden(X17,X15)|esk1_1(X15)!=k3_mcart_1(X17,X18,X19)|X15=k1_xboole_0)&(~r2_hidden(X18,X15)|esk1_1(X15)!=k3_mcart_1(X17,X18,X19)|X15=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.20/0.41  fof(c_0_36, plain, ![X25, X26]:(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|k1_orders_2(X25,X26)=a_2_0_orders_2(X25,X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (k1_orders_2(esk4_0,k1_struct_0(esk4_0))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.20/0.41  cnf(c_0_38, plain, (k1_struct_0(X1)=k1_xboole_0|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  fof(c_0_39, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.41  cnf(c_0_40, plain, (r2_orders_2(X2,X1,esk2_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_41, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_42, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_0_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  cnf(c_0_45, plain, (v2_struct_0(X1)|m1_subset_1(esk2_3(X2,X1,u1_struct_0(X1)),u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X2,a_2_0_orders_2(X1,u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.41  cnf(c_0_46, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_47, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k1_orders_2(esk4_0,k1_xboole_0)=u1_struct_0(esk4_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.41  cnf(c_0_49, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.41  fof(c_0_50, plain, ![X27]:(~l1_orders_2(X27)|l1_struct_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.41  cnf(c_0_51, plain, (v2_struct_0(X1)|r2_orders_2(X1,X2,esk2_3(X3,X1,X4))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X3,a_2_0_orders_2(X1,X4))|~r2_hidden(X2,X4)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_52, plain, (v2_struct_0(X1)|r2_hidden(esk3_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_53, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.41  cnf(c_0_54, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|m1_subset_1(esk2_3(esk1_1(a_2_0_orders_2(X1,u1_struct_0(X1))),X1,u1_struct_0(X1)),u1_struct_0(X1))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (a_2_0_orders_2(esk4_0,k1_xboole_0)=u1_struct_0(esk4_0)|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_49])]), c_0_28])).
% 0.20/0.41  cnf(c_0_56, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.41  fof(c_0_57, plain, ![X21]:(~l1_struct_0(X21)|k2_struct_0(X21)=u1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.41  fof(c_0_58, plain, ![X22, X23, X24]:(((r1_orders_2(X22,X23,X24)|~r2_orders_2(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|~l1_orders_2(X22))&(X23!=X24|~r2_orders_2(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|~l1_orders_2(X22)))&(~r1_orders_2(X22,X23,X24)|X23=X24|r2_orders_2(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~m1_subset_1(X23,u1_struct_0(X22))|~l1_orders_2(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.20/0.41  cnf(c_0_59, plain, (v2_struct_0(X1)|r2_orders_2(X1,X2,esk2_3(X3,X1,u1_struct_0(X1)))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X3,a_2_0_orders_2(X1,u1_struct_0(X1)))|~r2_hidden(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_51, c_0_34])).
% 0.20/0.41  cnf(c_0_60, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_0_orders_2(X1,k1_xboole_0))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_53])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))=k1_xboole_0|m1_subset_1(esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (a_2_0_orders_2(esk4_0,k1_xboole_0)=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_27])])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (k1_orders_2(esk4_0,k2_struct_0(esk4_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_64, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.41  cnf(c_0_65, plain, (k1_orders_2(X1,u1_struct_0(X1))=a_2_0_orders_2(X1,u1_struct_0(X1))|v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_47, c_0_34])).
% 0.20/0.41  cnf(c_0_66, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  cnf(c_0_67, plain, (a_2_0_orders_2(X1,u1_struct_0(X1))=k1_xboole_0|v2_struct_0(X1)|r2_orders_2(X1,X2,esk2_3(esk1_1(a_2_0_orders_2(X1,u1_struct_0(X1))),X1,u1_struct_0(X1)))|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))=k1_xboole_0|r2_hidden(esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (k1_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (k1_orders_2(esk4_0,u1_struct_0(esk4_0))=a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.20/0.41  cnf(c_0_71, plain, (~r2_orders_2(X1,X2,X2)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_66])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))=k1_xboole_0|r2_orders_2(esk4_0,esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)),esk2_3(esk1_1(a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))),esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_24]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))!=k1_xboole_0|~l1_struct_0(esk4_0)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (a_2_0_orders_2(esk4_0,u1_struct_0(esk4_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_27])]), c_0_61])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_56]), c_0_27])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 77
% 0.20/0.41  # Proof object clause steps            : 46
% 0.20/0.41  # Proof object formula steps           : 31
% 0.20/0.41  # Proof object conjectures             : 22
% 0.20/0.41  # Proof object clause conjectures      : 19
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 22
% 0.20/0.41  # Proof object initial formulas used   : 15
% 0.20/0.41  # Proof object generating inferences   : 18
% 0.20/0.41  # Proof object simplifying inferences  : 50
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 15
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 29
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 28
% 0.20/0.41  # Processed clauses                    : 129
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 31
% 0.20/0.41  # ...remaining for further processing  : 98
% 0.20/0.41  # Other redundant clauses eliminated   : 4
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 1
% 0.20/0.41  # Backward-rewritten                   : 13
% 0.20/0.41  # Generated clauses                    : 182
% 0.20/0.41  # ...of the previous two non-trivial   : 175
% 0.20/0.41  # Contextual simplify-reflections      : 5
% 0.20/0.41  # Paramodulations                      : 178
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 4
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 80
% 0.20/0.41  #    Positive orientable unit clauses  : 11
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 4
% 0.20/0.41  #    Non-unit-clauses                  : 65
% 0.20/0.41  # Current number of unprocessed clauses: 74
% 0.20/0.41  # ...number of literals in the above   : 400
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 15
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 2403
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 316
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 33
% 0.20/0.41  # Unit Clause-clause subsumption calls : 102
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 5
% 0.20/0.41  # BW rewrite match successes           : 4
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 9368
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.066 s
% 0.20/0.41  # System time              : 0.003 s
% 0.20/0.41  # Total time               : 0.070 s
% 0.20/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:57 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 136 expanded)
%              Number of clauses        :   41 (  58 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 341 expanded)
%              Number of equality atoms :   46 (  84 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t6_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc12_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(c_0_16,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk3_2(X18,X19),X19)
        | esk3_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk3_2(X18,X19),X19)
        | esk3_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

cnf(c_0_21,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk5_0,esk4_0)
    & v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0)
    & v1_zfmisc_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_26,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_27,plain,
    ( k6_domain_1(X1,X2) = k1_enumset1(X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X24,X25] :
      ( ~ v1_xboole_0(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | v1_xboole_0(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_32,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk5_0) = k6_domain_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_35,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_36,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_22]),c_0_23])).

fof(c_0_38,plain,(
    ! [X37,X38] :
      ( v1_xboole_0(X37)
      | v1_xboole_0(X38)
      | ~ v1_zfmisc_1(X38)
      | ~ r1_tarski(X37,X38)
      | X37 = X38 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,k6_domain_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

fof(c_0_45,plain,(
    ! [X32] :
      ( ~ l1_orders_2(X32)
      | l1_struct_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_46,plain,(
    ! [X35] :
      ( v1_orders_2(k2_yellow_1(X35))
      & l1_orders_2(k2_yellow_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( esk2_2(k6_domain_1(esk4_0,esk5_0),X1) = esk5_0
    | r1_tarski(k6_domain_1(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k1_enumset1(X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_52,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_53,plain,(
    ! [X31] :
      ( ~ l1_struct_0(X31)
      | ~ v1_subset_1(k2_struct_0(X31),u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).

fof(c_0_54,plain,(
    ! [X36] :
      ( u1_struct_0(k2_yellow_1(X36)) = X36
      & u1_orders_2(k2_yellow_1(X36)) = k1_yellow_1(X36) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

cnf(c_0_55,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( X1 = X2
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k6_domain_1(esk4_0,esk5_0),X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(k6_domain_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_34])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( ~ l1_struct_0(X1)
    | ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( l1_struct_0(k2_yellow_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_64,plain,(
    ! [X30] :
      ( ~ l1_struct_0(X30)
      | k2_struct_0(X30) = u1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_65,negated_conjecture,
    ( k6_domain_1(esk4_0,esk5_0) = X1
    | ~ v1_zfmisc_1(X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_28]),c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_68,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_69,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_71,negated_conjecture,
    ( k6_domain_1(esk4_0,esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_72,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_62]),c_0_63])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.37  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 0.13/0.37  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.13/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.37  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 0.13/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.37  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.13/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.37  fof(fc12_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>~(v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 0.13/0.37  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.13/0.37  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.37  fof(c_0_16, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|X16=X14|X15!=k1_tarski(X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_tarski(X14)))&((~r2_hidden(esk3_2(X18,X19),X19)|esk3_2(X18,X19)!=X18|X19=k1_tarski(X18))&(r2_hidden(esk3_2(X18,X19),X19)|esk3_2(X18,X19)=X18|X19=k1_tarski(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.37  fof(c_0_17, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_18, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_19, plain, ![X33, X34]:(v1_xboole_0(X33)|~m1_subset_1(X34,X33)|k6_domain_1(X33,X34)=k1_tarski(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.37  fof(c_0_20, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.13/0.37  cnf(c_0_21, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_24, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  fof(c_0_25, negated_conjecture, (~v1_xboole_0(esk4_0)&(m1_subset_1(esk5_0,esk4_0)&(v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0)&v1_zfmisc_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.13/0.37  cnf(c_0_26, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.13/0.37  cnf(c_0_27, plain, (k6_domain_1(X1,X2)=k1_enumset1(X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_22]), c_0_23])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  fof(c_0_31, plain, ![X24, X25]:(~v1_xboole_0(X24)|(~m1_subset_1(X25,k1_zfmisc_1(X24))|v1_xboole_0(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.13/0.37  fof(c_0_32, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.37  cnf(c_0_33, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk5_0)=k6_domain_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.13/0.37  fof(c_0_35, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  fof(c_0_36, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.37  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_22]), c_0_23])).
% 0.13/0.37  fof(c_0_38, plain, ![X37, X38]:(v1_xboole_0(X37)|(v1_xboole_0(X38)|~v1_zfmisc_1(X38)|(~r1_tarski(X37,X38)|X37=X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.13/0.37  cnf(c_0_39, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,k6_domain_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.37  cnf(c_0_42, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_43, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.37  cnf(c_0_44, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).
% 0.13/0.37  fof(c_0_45, plain, ![X32]:(~l1_orders_2(X32)|l1_struct_0(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.37  fof(c_0_46, plain, ![X35]:(v1_orders_2(k2_yellow_1(X35))&l1_orders_2(k2_yellow_1(X35))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.13/0.37  cnf(c_0_47, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.37  cnf(c_0_48, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.37  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (esk2_2(k6_domain_1(esk4_0,esk5_0),X1)=esk5_0|r1_tarski(k6_domain_1(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.37  cnf(c_0_51, plain, (~v1_xboole_0(k1_enumset1(X1,X1,X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.37  fof(c_0_52, plain, ![X26, X27]:(~m1_subset_1(X26,X27)|(v1_xboole_0(X27)|r2_hidden(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.37  fof(c_0_53, plain, ![X31]:(~l1_struct_0(X31)|~v1_subset_1(k2_struct_0(X31),u1_struct_0(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).
% 0.13/0.37  fof(c_0_54, plain, ![X36]:(u1_struct_0(k2_yellow_1(X36))=X36&u1_orders_2(k2_yellow_1(X36))=k1_yellow_1(X36)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.13/0.37  cnf(c_0_55, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.37  cnf(c_0_56, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.37  cnf(c_0_57, plain, (X1=X2|v1_xboole_0(X1)|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (r1_tarski(k6_domain_1(esk4_0,esk5_0),X1)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.37  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(k6_domain_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_34])).
% 0.13/0.37  cnf(c_0_60, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.37  cnf(c_0_61, plain, (~l1_struct_0(X1)|~v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.37  cnf(c_0_62, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.37  cnf(c_0_63, plain, (l1_struct_0(k2_yellow_1(X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.37  fof(c_0_64, plain, ![X30]:(~l1_struct_0(X30)|k2_struct_0(X30)=u1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.37  cnf(c_0_65, negated_conjecture, (k6_domain_1(esk4_0,esk5_0)=X1|~v1_zfmisc_1(X1)|~r2_hidden(esk5_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.13/0.37  cnf(c_0_66, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_28]), c_0_29])).
% 0.13/0.37  cnf(c_0_67, negated_conjecture, (v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_68, plain, (~v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.13/0.37  cnf(c_0_69, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.37  cnf(c_0_70, negated_conjecture, (v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_71, negated_conjecture, (k6_domain_1(esk4_0,esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.13/0.37  cnf(c_0_72, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_62]), c_0_63])])).
% 0.13/0.37  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_72]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 74
% 0.13/0.37  # Proof object clause steps            : 41
% 0.13/0.37  # Proof object formula steps           : 33
% 0.13/0.37  # Proof object conjectures             : 16
% 0.13/0.37  # Proof object clause conjectures      : 13
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 21
% 0.13/0.37  # Proof object initial formulas used   : 16
% 0.13/0.37  # Proof object generating inferences   : 13
% 0.13/0.37  # Proof object simplifying inferences  : 22
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 16
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 28
% 0.13/0.37  # Removed in clause preprocessing      : 3
% 0.13/0.37  # Initial clauses in saturation        : 25
% 0.13/0.37  # Processed clauses                    : 79
% 0.13/0.37  # ...of these trivial                  : 2
% 0.13/0.37  # ...subsumed                          : 5
% 0.13/0.37  # ...remaining for further processing  : 72
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 9
% 0.13/0.37  # Generated clauses                    : 45
% 0.13/0.37  # ...of the previous two non-trivial   : 42
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 43
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 3
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 36
% 0.13/0.37  #    Positive orientable unit clauses  : 11
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 4
% 0.13/0.37  #    Non-unit-clauses                  : 21
% 0.13/0.37  # Current number of unprocessed clauses: 6
% 0.13/0.37  # ...number of literals in the above   : 17
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 37
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 149
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 93
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.37  # Unit Clause-clause subsumption calls : 22
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 4
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2254
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.028 s
% 0.13/0.37  # System time              : 0.007 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------

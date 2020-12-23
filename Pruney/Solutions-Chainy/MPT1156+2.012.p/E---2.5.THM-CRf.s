%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:48 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 145 expanded)
%              Number of clauses        :   34 (  50 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  257 ( 713 expanded)
%              Number of equality atoms :   87 (  87 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

fof(t35_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
            & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

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

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t49_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ~ ( r2_hidden(X2,X3)
                  & r2_hidden(X2,k2_orders_2(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ~ r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t50_orders_2])).

fof(c_0_17,plain,(
    ! [X74,X75] :
      ( ( v6_orders_2(k6_domain_1(u1_struct_0(X74),X75),X74)
        | ~ m1_subset_1(X75,u1_struct_0(X74))
        | v2_struct_0(X74)
        | ~ v3_orders_2(X74)
        | ~ l1_orders_2(X74) )
      & ( m1_subset_1(k6_domain_1(u1_struct_0(X74),X75),k1_zfmisc_1(u1_struct_0(X74)))
        | ~ m1_subset_1(X75,u1_struct_0(X74))
        | v2_struct_0(X74)
        | ~ v3_orders_2(X74)
        | ~ l1_orders_2(X74) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & r2_hidden(esk4_0,k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X70,X71] :
      ( v2_struct_0(X70)
      | ~ v3_orders_2(X70)
      | ~ v4_orders_2(X70)
      | ~ v5_orders_2(X70)
      | ~ l1_orders_2(X70)
      | ~ m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))
      | m1_subset_1(k2_orders_2(X70,X71),k1_zfmisc_1(u1_struct_0(X70))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X64,X65,X66] :
      ( ~ m1_subset_1(X65,k1_zfmisc_1(X64))
      | ~ r2_hidden(X66,X65)
      | r2_hidden(X66,X64) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X76,X77,X78] :
      ( v2_struct_0(X76)
      | ~ v3_orders_2(X76)
      | ~ v4_orders_2(X76)
      | ~ v5_orders_2(X76)
      | ~ l1_orders_2(X76)
      | ~ m1_subset_1(X77,u1_struct_0(X76))
      | ~ m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X76)))
      | ~ r2_hidden(X77,X78)
      | ~ r2_hidden(X77,k2_orders_2(X76,X78)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_orders_2])])])])).

fof(c_0_31,plain,(
    ! [X67,X68,X69] :
      ( ~ r2_hidden(X67,X68)
      | ~ m1_subset_1(X68,k1_zfmisc_1(X69))
      | m1_subset_1(X67,X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22]),c_0_28]),c_0_29]),c_0_23])]),c_0_24])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k2_orders_2(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X72,X73] :
      ( v1_xboole_0(X72)
      | ~ m1_subset_1(X73,X72)
      | k6_domain_1(X72,X73) = k1_tarski(X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_37,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_39,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_40,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_41,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_42,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_43,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42) = k5_enumset1(X36,X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_44,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v1_xboole_0(X11)
        | ~ r2_hidden(X12,X11) )
      & ( r2_hidden(esk1_1(X13),X13)
        | v1_xboole_0(X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k2_orders_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_58,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62] :
      ( ( ~ r2_hidden(X52,X51)
        | X52 = X43
        | X52 = X44
        | X52 = X45
        | X52 = X46
        | X52 = X47
        | X52 = X48
        | X52 = X49
        | X52 = X50
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X43
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X44
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X45
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X46
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X47
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X48
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X49
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( X53 != X50
        | r2_hidden(X53,X51)
        | X51 != k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50) )
      & ( esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X54
        | ~ r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X55
        | ~ r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X56
        | ~ r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X57
        | ~ r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X58
        | ~ r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X59
        | ~ r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X60
        | ~ r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) != X61
        | ~ r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) )
      & ( r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)
        | esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X54
        | esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X55
        | esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X56
        | esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X57
        | esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X58
        | esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X59
        | esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X60
        | esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62) = X61
        | X62 = k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(X1,k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_22]),c_0_28]),c_0_29]),c_0_23])]),c_0_24])).

cnf(c_0_60,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_64,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk4_0) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_21]),c_0_61])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:45:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.029 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t50_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 0.19/0.37  fof(t35_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 0.19/0.37  fof(dt_k2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 0.19/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.37  fof(t49_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k2_orders_2(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 0.19/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.37  fof(d6_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:(X9=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)<=>![X10]:(r2_hidden(X10,X9)<=>~((((((((X10!=X1&X10!=X2)&X10!=X3)&X10!=X4)&X10!=X5)&X10!=X6)&X10!=X7)&X10!=X8)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 0.19/0.37  fof(c_0_16, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))))))), inference(assume_negation,[status(cth)],[t50_orders_2])).
% 0.19/0.37  fof(c_0_17, plain, ![X74, X75]:((v6_orders_2(k6_domain_1(u1_struct_0(X74),X75),X74)|~m1_subset_1(X75,u1_struct_0(X74))|(v2_struct_0(X74)|~v3_orders_2(X74)|~l1_orders_2(X74)))&(m1_subset_1(k6_domain_1(u1_struct_0(X74),X75),k1_zfmisc_1(u1_struct_0(X74)))|~m1_subset_1(X75,u1_struct_0(X74))|(v2_struct_0(X74)|~v3_orders_2(X74)|~l1_orders_2(X74)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).
% 0.19/0.37  fof(c_0_18, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&r2_hidden(esk4_0,k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.19/0.37  fof(c_0_19, plain, ![X70, X71]:(v2_struct_0(X70)|~v3_orders_2(X70)|~v4_orders_2(X70)|~v5_orders_2(X70)|~l1_orders_2(X70)|~m1_subset_1(X71,k1_zfmisc_1(u1_struct_0(X70)))|m1_subset_1(k2_orders_2(X70,X71),k1_zfmisc_1(u1_struct_0(X70)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).
% 0.19/0.37  cnf(c_0_20, plain, (m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  fof(c_0_25, plain, ![X64, X65, X66]:(~m1_subset_1(X65,k1_zfmisc_1(X64))|(~r2_hidden(X66,X65)|r2_hidden(X66,X64))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.37  cnf(c_0_26, plain, (v2_struct_0(X1)|m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  fof(c_0_30, plain, ![X76, X77, X78]:(v2_struct_0(X76)|~v3_orders_2(X76)|~v4_orders_2(X76)|~v5_orders_2(X76)|~l1_orders_2(X76)|(~m1_subset_1(X77,u1_struct_0(X76))|(~m1_subset_1(X78,k1_zfmisc_1(u1_struct_0(X76)))|(~r2_hidden(X77,X78)|~r2_hidden(X77,k2_orders_2(X76,X78)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_orders_2])])])])).
% 0.19/0.37  fof(c_0_31, plain, ![X67, X68, X69]:(~r2_hidden(X67,X68)|~m1_subset_1(X68,k1_zfmisc_1(X69))|m1_subset_1(X67,X69)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.37  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (m1_subset_1(k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22]), c_0_28]), c_0_29]), c_0_23])]), c_0_24])).
% 0.19/0.37  cnf(c_0_34, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,X3)|~r2_hidden(X2,k2_orders_2(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  cnf(c_0_35, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  fof(c_0_36, plain, ![X72, X73]:(v1_xboole_0(X72)|~m1_subset_1(X73,X72)|k6_domain_1(X72,X73)=k1_tarski(X73)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.37  fof(c_0_37, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_38, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_39, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  fof(c_0_40, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.37  fof(c_0_41, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.37  fof(c_0_42, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.37  fof(c_0_43, plain, ![X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42)=k5_enumset1(X36,X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.37  fof(c_0_44, plain, ![X11, X12, X13]:((~v1_xboole_0(X11)|~r2_hidden(X12,X11))&(r2_hidden(esk1_1(X13),X13)|v1_xboole_0(X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_0,k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_47, plain, (v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,k2_orders_2(X1,X2))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  cnf(c_0_48, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  cnf(c_0_50, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.37  cnf(c_0_51, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.37  cnf(c_0_52, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.37  cnf(c_0_53, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.37  cnf(c_0_54, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.37  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.37  cnf(c_0_56, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.37  fof(c_0_58, plain, ![X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62]:(((~r2_hidden(X52,X51)|(X52=X43|X52=X44|X52=X45|X52=X46|X52=X47|X52=X48|X52=X49|X52=X50)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50))&((((((((X53!=X43|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50))&(X53!=X44|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X45|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X46|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X47|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X48|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X49|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50)))&(X53!=X50|r2_hidden(X53,X51)|X51!=k6_enumset1(X43,X44,X45,X46,X47,X48,X49,X50))))&(((((((((esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X54|~r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61))&(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X55|~r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X56|~r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X57|~r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X58|~r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X59|~r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X60|~r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)!=X61|~r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))&(r2_hidden(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62),X62)|(esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X54|esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X55|esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X56|esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X57|esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X58|esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X59|esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X60|esk2_9(X54,X55,X56,X57,X58,X59,X60,X61,X62)=X61)|X62=k6_enumset1(X54,X55,X56,X57,X58,X59,X60,X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (~r2_hidden(X1,k2_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk3_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_27]), c_0_22]), c_0_28]), c_0_29]), c_0_23])]), c_0_24])).
% 0.19/0.37  cnf(c_0_60, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.37  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (~r2_hidden(esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 0.19/0.37  cnf(c_0_64, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk4_0)=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_21]), c_0_61])).
% 0.19/0.37  cnf(c_0_65, plain, (r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_65])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 67
% 0.19/0.37  # Proof object clause steps            : 34
% 0.19/0.37  # Proof object formula steps           : 33
% 0.19/0.37  # Proof object conjectures             : 19
% 0.19/0.37  # Proof object clause conjectures      : 16
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 22
% 0.19/0.37  # Proof object initial formulas used   : 16
% 0.19/0.37  # Proof object generating inferences   : 8
% 0.19/0.37  # Proof object simplifying inferences  : 30
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 16
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 41
% 0.19/0.37  # Removed in clause preprocessing      : 7
% 0.19/0.37  # Initial clauses in saturation        : 34
% 0.19/0.37  # Processed clauses                    : 106
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 9
% 0.19/0.37  # ...remaining for further processing  : 97
% 0.19/0.37  # Other redundant clauses eliminated   : 17
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 27
% 0.19/0.37  # Generated clauses                    : 70
% 0.19/0.37  # ...of the previous two non-trivial   : 69
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 61
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 17
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 27
% 0.19/0.37  #    Positive orientable unit clauses  : 15
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 9
% 0.19/0.37  # Current number of unprocessed clauses: 28
% 0.19/0.37  # ...number of literals in the above   : 80
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 68
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 250
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 132
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 36
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 57
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 4622
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.033 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.038 s
% 0.19/0.37  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
